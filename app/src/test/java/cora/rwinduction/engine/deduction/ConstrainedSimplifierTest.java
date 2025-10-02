/**************************************************************************************************
 Copyright 2024-2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rwinduction.engine.deduction;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import java.util.Optional;
import java.util.function.Function;

import charlie.util.Pair;
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.*;
import charlie.substitution.MutableSubstitution;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.SmtProblem;
import charlie.smt.SmtSolver;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class ConstrainedSimplifierTest {
  private TRS _trs;

  private TRS setupTRS() {
    if (_trs == null) _trs = CoraInputReader.readTrsFromString(
      "sum1 :: Int -> Int\n" +
      "sum1(x) -> 0 | x <= 0\n" +
      "sum1(x) -> x + sum1(x-1) | x > 0\n" +
      "sum2 :: Int -> Int\n" +
      "sum2(x) -> iter(y, i, z) | i = 0 ∧ i + 1 = a ∧ y = x ∧ z = a - 1\n" +
      "iter :: Int -> Int -> Int -> Int\n");
    return _trs;
  }

  public PartialProof setupProof(String eqdesc) {
    TRS trs = setupTRS();
    TermPrinter printer = new TermPrinter(trs.queryFunctionSymbolNames());
    return new PartialProof(trs, EquationParser.parseEquationList(eqdesc, trs),
                            lst -> printer.generateUniqueNaming(lst));
  }

  @Test
  public void testConstraintIsTrue() {
    PartialProof pp = setupProof("sum1(x) = sum2(x)");
    ConstrainedSimplifier simp = new ConstrainedSimplifier(
      pp.getProofState().getTopEquation().getLhs(),
      pp.getProofState().getTopEquation().getRhs(),
      pp.getProofState().getTopEquation().getConstraint(),
      pp.getProofState().getTopEquation().getRenaming(), null);
    assertTrue(simp.constraintIsTrue());
    pp = setupProof("sum1(x) = sum2(x) | x = x");
    simp = new ConstrainedSimplifier(
      pp.getProofState().getTopEquation().getLhs(),
      pp.getProofState().getTopEquation().getRhs(),
      pp.getProofState().getTopEquation().getConstraint(),
      pp.getProofState().getTopEquation().getRenaming(),
      new MutableSubstitution());
    assertFalse(simp.constraintIsTrue());
  }

  @Test
  public void testMissingAndMatchSides() {
    PartialProof pp = setupProof("sum2(u) = iter(u, 0, 0)");
    Rule rule = pp.getContext().getRule("O3");
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(pp.getContext().getRenaming("O3").getReplaceable("i"),
                 CoraInputReader.readTerm("0", pp.getContext().getRenaming("O3"), _trs));
    ConstrainedSimplifier simp = new ConstrainedSimplifier(rule.queryLeftSide(),
      rule.queryRightSide(), rule.queryConstraint(), pp.getContext().getRenaming("O3"), subst);
    assertTrue(simp.queryMissingReplaceables().toString().equals("[x, y, z, a]"));
    assertTrue(simp.matchLeft(pp.getProofState().getTopEquation().getLhs()) == null);
    assertTrue(subst.domain().size() == 1);
    assertTrue(simp.querySubstitution().domain().size() == 2);
    assertTrue(simp.queryMissingReplaceables().toString().equals("[y, z, a]"));
    assertTrue(simp.matchRight(pp.getProofState().getTopEquation().getRhs()) == null);
    assertTrue(simp.queryMissingReplaceables().toString().equals("[a]"));
    assertTrue(simp.querySubstitution().domain().size() == 4);
    assertTrue(simp.querySubstitution().get(pp.getContext().getRenaming("O3").getReplaceable("y"))
      == pp.getProofState().getTopEquation().getRenaming().getReplaceable("u"));
  }

  @Test
  public void testMatchFailure() {
    PartialProof pp = setupProof("sum2(z) = iter(z, 0, 0) | z < 0");
    Rule rule = pp.getContext().getRule("O3");
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(pp.getContext().getRenaming("O3").getReplaceable("x"),
                 CoraInputReader.readTerm("0", pp.getContext().getRenaming("O3"), _trs));
    ConstrainedSimplifier simp = new ConstrainedSimplifier(rule.queryLeftSide(),
      rule.queryRightSide(), rule.queryConstraint(), pp.getContext().getRenaming("O3"), subst);
    assertTrue(simp.matchLeft(pp.getProofState().getTopEquation().getLhs()).toString().equals(
      "Variable x is mapped both to 0 and to z."));
  }

  @Test
  public void testMatchEqualities() {
    PartialProof pp = setupProof(
      "iter(x, y, 0) = iter(y, z, a) | x > 0 ∧ a = z + 1 ∧ y != -3 ∧ z = x - y ∧ y != -3");

    MutableRenaming renaming = new MutableRenaming(_trs.queryFunctionSymbolNames());
    Term left = CoraInputReader.readTermAndUpdateNaming("iter(a, b, c)", renaming, _trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("iter(a, d, e)", renaming, _trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming(
      "a > 1 ∧ d = a - b ∧ b != 0 ∧ d + 1 = e", renaming, _trs);
    ConstrainedSimplifier simp = new ConstrainedSimplifier(left, right, constraint, renaming,
                                                           new MutableSubstitution());
    assertTrue(simp.matchLeft(pp.getProofState().getTopEquation().getLhs()) == null);
    assertTrue(simp.matchEqualitiesInConstraint(
      pp.getProofState().getTopEquation().getConstraint()));
    Renaming eqnaming = pp.getProofState().getTopEquation().getRenaming();
    var gamma = simp.querySubstitution();
    assertTrue(gamma.get(renaming.getReplaceable("a")) == eqnaming.getReplaceable("x"));
    assertTrue(gamma.get(renaming.getReplaceable("b")) == eqnaming.getReplaceable("y"));
    assertTrue(gamma.get(renaming.getReplaceable("c")).isValue());
    assertTrue(gamma.get(renaming.getReplaceable("d")) == eqnaming.getReplaceable("z"));
    assertTrue(gamma.get(renaming.getReplaceable("e")) == eqnaming.getReplaceable("a"));
    Function<Variable,Pair<Variable,String>> myfun = x -> new Pair<Variable,String>(x, "");
    assertTrue(simp.addDefinitionsToSubstitution(myfun).size() == 0);
  }

  @Test
  public void testOnlyCalculations() {
    PartialProof pp = setupProof("sum2(u) = iter(u, 0, 0)");
    Rule rule = pp.getContext().getRule("O3");
    // sum2(x) -> iter(y, i, z) | i = 0 ∧ i + 1 = a ∧ y = x ∧ z = a - 1
    ConstrainedSimplifier simp = new ConstrainedSimplifier(rule.queryLeftSide(),
      rule.queryRightSide(), rule.queryConstraint(), pp.getContext().getRenaming("O3"), null);
    simp.matchLeft(pp.getProofState().getTopEquation().getLhs());
    assertTrue(simp.matchEqualitiesInConstraint(
      pp.getProofState().getTopEquation().getConstraint()));
    var gamma = simp.querySubstitution();
    assertTrue(gamma.domain().size() == 4);
    assertTrue(gamma.get(simp.queryRenaming().getReplaceable("i")).toValue().getInt() == 0);
    assertTrue(gamma.get(simp.queryRenaming().getReplaceable("a")).toValue().getInt() == 1);
    assertTrue(gamma.get(simp.queryRenaming().getReplaceable("z")).toValue().getInt() == 0);
    assertTrue(!gamma.domain().contains(simp.queryRenaming().getReplaceable("y")));
  }

  @Test
  public void testAddDefinitionsToSubstitution() {
    PartialProof pp = setupProof("sum2(u) = iter(u, 0, 0)");
    Rule rule = pp.getContext().getRule("O3");
    // sum2(x) -> iter(y, i, z) | i = 0 ∧ i + 1 = a ∧ y = x ∧ z = a - 1
    ConstrainedSimplifier simp = new ConstrainedSimplifier(rule.queryLeftSide(),
      rule.queryRightSide(), rule.queryConstraint(), pp.getContext().getRenaming("O3"), null);
    simp.matchLeft(pp.getProofState().getTopEquation().getLhs());

    MutableRenaming renaming = pp.getProofState().getTopEquation().getRenaming().copy();
    renaming.setName(simp.queryRenaming().getReplaceable("a"), "a");
    VariableNamer namer = pp.getContext().getVariableNamer();
    Function<Variable,Pair<Variable,String>> chooser = x -> {
      Variable y = namer.chooseDerivativeOrSameNaming(x, renaming, x.queryType());
      return new Pair<Variable,String>(y, renaming.getName(y));
    };
    ArrayList<Pair<Pair<Variable,String>,Term>> lst = simp.addDefinitionsToSubstitution(chooser);
    assertTrue(lst != null);
    assertTrue(simp.querySubstitution().domain().size() == 5);
    assertTrue(lst.size() == 4);
  }

  @Test
  public void testConstraintVariableNotSubstituted() {
    PartialProof pp = setupProof("sum1(z) + 0 = iter(z, 0, 0) | z < 0");
    MutableRenaming renaming = new MutableRenaming(_trs.queryFunctionSymbolNames());
    Term left = CoraInputReader.readTermAndUpdateNaming("iter(x, 0, 0)", renaming, _trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("iter(x, y, z)", renaming, _trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("z > 0 ∧ a != 0", renaming, _trs);
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(renaming.getReplaceable("x"), TheoryFactory.createValue(7));
    subst.extend(renaming.getReplaceable("z"), TheoryFactory.createValue(13));
    ConstrainedSimplifier simp = new ConstrainedSimplifier(left, right, constraint, renaming, null);
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    assertFalse(simp.canReduceCtermWithConstraint(TheoryFactory.trueValue, null, null, o, "XX"));
    assertTrue(module.toString().equals("The XX does not apply: constraint variable z is not " +
      "mapped to anything.\n\n"));
  }

  private class MySmtSolver implements SmtSolver {
    private boolean _answer;
    String _question;
    public MySmtSolver(boolean answer) { _answer = answer; _question = null; }
    public Answer checkSatisfiability(SmtProblem problem) { assertTrue(false); return null; }
    public boolean checkValidity(SmtProblem prob) { _question = prob.toString(); return _answer; }
  }

  @Test
  public void testConstraintSatisfaction() {
    PartialProof pp = setupProof("sum1(z) + 0 = iter(z, 0, 0) | z < 0");
    MutableRenaming renaming = new MutableRenaming(_trs.queryFunctionSymbolNames());
    Term left = CoraInputReader.readTermAndUpdateNaming("iter(x, 0, 0)", renaming, _trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("iter(x, y, z)", renaming, _trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("z > 0 ∧ a != 0", renaming, _trs);
    Renaming eqnaming = pp.getProofState().getTopEquation().getRenaming();
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(renaming.getReplaceable("z"), TheoryFactory.createValue(7));
    subst.extend(renaming.getReplaceable("a"), (Variable)eqnaming.getReplaceable("z"));
    subst.extend(renaming.getReplaceable("x"), (Variable)eqnaming.getReplaceable("z"));
    ConstrainedSimplifier simp = new ConstrainedSimplifier(left,right,constraint,renaming,subst);
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    MySmtSolver solver = new MySmtSolver(true);
    assertTrue(simp.canReduceCtermWithConstraint(
      pp.getProofState().getTopEquation().getConstraint(), solver, eqnaming, o, "XX"));
    assertTrue(module.toString().equals(""));
    assertTrue(solver._question.equals("(i1 >= 0) or ((6 >= 0) and (i1 # 0))\n"));

    solver = new MySmtSolver(false);
    assertFalse(simp.canReduceCtermWithConstraint(
      pp.getProofState().getTopEquation().getConstraint(), solver, eqnaming, o, "XX"));
    assertTrue(module.toString().equals(
      "The XX does not apply: I could not prove that z < 0 ⊨ 7 > 0 nor z < 0 ⊨ z ≠ 0.\n\n"));
  }

  @Test
  public void testConstraintVariableMappedToComplexTerm() {
    PartialProof pp = setupProof("sum1(z) = 0 + sum1(z) | z < 0");
    Rule rule = pp.getContext().getRule("O1");
    MutableSubstitution subst = new MutableSubstitution();
    Renaming eqnaming = pp.getProofState().getTopEquation().getRenaming();
    subst.extend(pp.getContext().getRenaming("O1").getReplaceable("x"),
                 CoraInputReader.readTerm("z + 0", eqnaming, _trs));
    ConstrainedSimplifier simp = new ConstrainedSimplifier(rule.queryLeftSide(),
      rule.queryRightSide(), rule.queryConstraint(), pp.getContext().getRenaming("O1"), subst);
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    MySmtSolver solver = new MySmtSolver(true);
    assertFalse(simp.canReduceCtermWithConstraint(
      pp.getProofState().getTopEquation().getConstraint(), solver, eqnaming, o, "XXX"));
    assertTrue(solver._question == null);
    assertTrue(module.toString().equals("The XXX does not apply: constraint variable x is " +
      "instantiated by z + 0, which is not a value or variable.\n\n"));
  }

  @Test
  public void testSemiSubstitution() {
    PartialProof pp = setupProof("sum2(sum2(0)) = 0");
    Rule rule = pp.getContext().getRule("O3");
    Renaming eqnaming = pp.getProofState().getTopEquation().getRenaming();
    ConstrainedSimplifier simp = new ConstrainedSimplifier(rule.queryLeftSide(),
      rule.queryRightSide(), rule.queryConstraint(), pp.getContext().getRenaming("O3"), null);
    assertTrue(simp.matchLeft(pp.getProofState().getTopEquation().getLhs()) == null);
    assertFalse(simp.checkSemiConstructorSubstitution(pp.getContext()));
    simp.replaceSubstitution(new MutableSubstitution());
    assertTrue(simp.matchLeft(pp.getProofState().getTopEquation().getLhs().queryArgument(1))
               == null);
    assertTrue(simp.checkSemiConstructorSubstitution(pp.getContext()));
  }
}

