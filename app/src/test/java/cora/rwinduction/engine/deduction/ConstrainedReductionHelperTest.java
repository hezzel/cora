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
import java.util.List;
import java.util.Set;
import java.util.Optional;

import charlie.exceptions.CustomParserException;
import charlie.terms.position.Position;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.Truth;
import charlie.smt.SmtProblem;
import charlie.smt.SmtSolver;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class ConstrainedReductionHelperTest {
  private TRS _trs;

  private TRS setupTRS() {
    if (_trs == null) _trs = CoraInputReader.readTrsFromString(
      "sum1 :: Int -> Int\n" +
      "sum1(x) -> 0 | x <= 0\n" +
      "sum1(x) -> x + sum1(x-1) | x > 0\n" +
      "sum2 :: Int -> Int\n" +
      "sum2(x) -> iter(x, 0, 0)\n" +
      "iter :: Int -> Int -> Int -> Int\n");
    return _trs;
  }

  public PartialProof setupProof(String eqdesc) {
    TRS trs = setupTRS();
    TermPrinter printer = new TermPrinter(trs.queryFunctionSymbolNames());
    return new PartialProof(trs, EquationParser.parseEquationList(eqdesc, trs),
                            lst -> printer.generateUniqueNaming(lst));
  }

  private class MySmtSolver implements SmtSolver {
    private boolean _answer;
    String _question;
    public MySmtSolver(boolean answer) { _answer = answer; _question = null; }
    public Answer checkSatisfiability(SmtProblem problem) { assertTrue(false); return null; }
    public boolean checkValidity(SmtProblem prob) { _question = prob.toString(); return _answer; }
  }

  @Test
  public void testExtendSubstitution() throws CustomParserException {
    PartialProof pp = setupProof("sum1(z) + 0 = iter(z, 0, 0) | z < 0");
    OutputModule module = OutputModule.createUnitTestModule();
    EquationPosition pos = new EquationPosition(EquationPosition.Side.Left, Position.parse("1"));
    Rule rule = pp.getContext().getRule("O2");
    Substitution subst = TermFactory.createEmptySubstitution();
    ConstrainedReductionHelper crh =
      new ConstrainedReductionHelper(rule.queryLeftSide(), rule.queryRightSide(),
        rule.queryConstraint(), pp.getContext().getRenaming("O2"), pos, subst, "rule");
    assertTrue(crh.querySubstitution().domain().isEmpty());
    subst.extend(TermFactory.createVar("a"), TermFactory.createVar("b"));
    assertTrue(crh.querySubstitution().domain().isEmpty());
    Optional<OutputModule> o = Optional.of(module);
    assertTrue(crh.extendSubstitution(pp.getProofState().getTopEquation().getEquation(), o));
    assertTrue(module.toString().equals(""));
  }

  @Test
  public void testFailToExtendSubstitution() throws CustomParserException {
    PartialProof pp = setupProof("sum1(z) + 0 = iter(z, 0, 0) | z < 0");
    OutputModule module = OutputModule.createUnitTestModule();
    EquationPosition pos = new EquationPosition(EquationPosition.Side.Left, Position.parse("1"));
    Rule rule = pp.getContext().getRule("O3");
    Substitution subst = TermFactory.createEmptySubstitution();
    ConstrainedReductionHelper crh =
      new ConstrainedReductionHelper(rule.queryLeftSide(), rule.queryRightSide(),
        rule.queryConstraint(), pp.getContext().getRenaming("O2"), pos, subst, "thingy");
    assertTrue(crh.querySubstitution().domain().isEmpty());
    Optional<OutputModule> o = Optional.of(module);
    assertFalse(crh.extendSubstitution(pp.getProofState().getTopEquation().getEquation(), o));
    assertTrue(module.toString().equals(
      "The thingy does not apply: constant sum2 is not instantiated by sum1.\n\n"));
  }

  @Test
  public void testExtendWithDefinitionsFromEquationConstraint() {
    PartialProof pp = setupProof(
      "iter(x, y, 0) = iter(y, z, a) | x > 0 ∧ a = z + 1 ∧ y != -3 ∧ z = x - y ∧ y != -3");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.TOPLEFT;
    Substitution subst = TermFactory.createEmptySubstitution();
    Renaming renaming = new Renaming(_trs.queryFunctionSymbolNames());
    Term left = CoraInputReader.readTermAndUpdateNaming("iter(a, b, c)", renaming, _trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("iter(a, d, e)", renaming, _trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming(
      "a > 1 ∧ d = a - b ∧ b != 0 ∧ d + 1 = e", renaming, _trs);
    ConstrainedReductionHelper crh =
      new ConstrainedReductionHelper(left, right, constraint, renaming, pos, subst, "XX");
    assertTrue(crh.extendSubstitution(pp.getProofState().getTopEquation().getEquation(), o));
    Renaming eqnaming = pp.getProofState().getTopEquation().getRenaming();
    Substitution gamma = crh.querySubstitution();
    assertTrue(gamma.get(renaming.getReplaceable("a")) == eqnaming.getReplaceable("x"));
    assertTrue(gamma.get(renaming.getReplaceable("b")) == eqnaming.getReplaceable("y"));
    assertTrue(gamma.get(renaming.getReplaceable("c")).isValue());
    assertTrue(gamma.get(renaming.getReplaceable("d")) == eqnaming.getReplaceable("z"));
    assertTrue(gamma.get(renaming.getReplaceable("e")) == eqnaming.getReplaceable("a"));
  }

  @Test
  public void testExtendWithCalculatedDefinitions() {
    PartialProof pp = setupProof("iter(x, 1, sum2(0)) = 0 | x != 0");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.TOPLEFT;
    Substitution subst = TermFactory.createEmptySubstitution();
    Renaming renaming = new Renaming(_trs.queryFunctionSymbolNames());
    Term left = CoraInputReader.readTermAndUpdateNaming("iter(a, b, q)", renaming, _trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("c + d", renaming, _trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming(
      "c = 0 ∧ d = b * 2 + c ∧ e = q + 2", renaming, _trs);
    ConstrainedReductionHelper crh =
      new ConstrainedReductionHelper(left, right, constraint, renaming, pos, subst, "XX");
    assertTrue(crh.extendSubstitution(pp.getProofState().getTopEquation().getEquation(), o));
    Substitution gamma = crh.querySubstitution();
    assertTrue(gamma.get(renaming.getReplaceable("b")).toValue().getInt() == 1);
    assertTrue(gamma.get(renaming.getReplaceable("c")).toValue().getInt() == 0);
    assertTrue(gamma.get(renaming.getReplaceable("d")).toValue().getInt() == 2);
    assertTrue(gamma.get(renaming.getReplaceable("e")) == null);
  }

  @Test
  public void testReduce() throws CustomParserException {
    PartialProof pp = setupProof("iter(z, 0, 0) = 9 + sum1(z) | z = -3");
    OutputModule module = OutputModule.createUnitTestModule();
    EquationPosition pos = new EquationPosition(EquationPosition.Side.Right, Position.parse("2"));
    Rule rule = pp.getContext().getRule("O2");
    Substitution subst = TermFactory.createEmptySubstitution();
    ConstrainedReductionHelper crh =
      new ConstrainedReductionHelper(rule.queryLeftSide(), rule.queryRightSide(),
        rule.queryConstraint(), pp.getContext().getRenaming("O2"), pos, subst, "thingy");
    Variable x = pp.getContext().getRenaming("O2").getVariable("x");
    subst.extend(x, TheoryFactory.createValue(37));
    Optional<OutputModule> o = Optional.of(module);
    // note that no checks are done in the reduce function!
    Equation eq = crh.reduce(pp.getProofState().getTopEquation().getEquation(), o);
    assertTrue(eq.toString().equals("iter(z, 0, 0) ≈ 9 + (x + sum1(x - 1)) | z = -3"));
    assertTrue(module.toString().equals(""));
  }

  @Test
  public void testVariableOnRightAndConstraintNotSubstituted() {
    PartialProof pp = setupProof("sum1(z) + 0 = iter(z, 0, 0) | z < 0");
    OutputModule module = OutputModule.createUnitTestModule();
    EquationPosition pos = EquationPosition.TOPLEFT;
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = new Renaming(_trs.queryFunctionSymbolNames());
    Term left = CoraInputReader.readTermAndUpdateNaming("iter(x, 0, 0)", renaming, _trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("iter(x, y, z)", renaming, _trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("z > 0 ∧ a != 0", renaming, _trs);
    Rule rule = pp.getContext().getRule("O4");
    Substitution subst = TermFactory.createEmptySubstitution();
    subst.extend(renaming.getVariable("x"), TheoryFactory.createValue(7));
    subst.extend(renaming.getVariable("z"), renaming.getVariable("z"));
    ConstrainedReductionHelper crh =
      new ConstrainedReductionHelper(left, right, constraint, renaming, pos, subst, "XX");
    assertFalse(crh.checkEverythingSubstituted(o));
    assertTrue(module.toString().equals("Not enough information given: I could not determine " +
      "the substitution to be used for y, a.\n\n"));
  }

  @Test
  public void testConstraintSatisfaction() {
    PartialProof pp = setupProof("sum1(z) + 0 = iter(z, 0, 0) | z < 0");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.TOPRIGHT;
    Renaming renaming = new Renaming(_trs.queryFunctionSymbolNames());
    Term left = CoraInputReader.readTermAndUpdateNaming("iter(x, 0, 0)", renaming, _trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("iter(x, y, z)", renaming, _trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("z > 0 ∧ a != 0", renaming, _trs);
    Renaming eqnaming = pp.getProofState().getTopEquation().getRenaming();
    Substitution subst = TermFactory.createEmptySubstitution();
    subst.extend(renaming.getVariable("z"), TheoryFactory.createValue(7));
    subst.extend(renaming.getVariable("a"), eqnaming.getVariable("z"));
    ConstrainedReductionHelper crh =
      new ConstrainedReductionHelper(left, right, constraint, renaming, pos, subst, "XX");
    assertTrue(crh.extendSubstitution(pp.getProofState().getTopEquation().getEquation(), o));
    MySmtSolver solver = new MySmtSolver(true);
    assertTrue(crh.checkConstraintGoodForReduction(
      pp.getProofState().getTopEquation().getEquation().getConstraint(), eqnaming, o, solver));
    assertTrue(module.toString().equals(""));
    assertTrue(solver._question.equals("(i1 >= 0) or ((6 >= 0) and (i1 # 0))\n"));

    solver = new MySmtSolver(false);
    assertFalse(crh.checkConstraintGoodForReduction(
      pp.getProofState().getTopEquation().getEquation().getConstraint(), eqnaming, o, solver));
    assertTrue(module.toString().equals(
      "The XX does not apply: I could not prove that z < 0 ⊨ 7 > 0 ∧ z ≠ 0.\n\n"));
  }

  @Test
  public void testConstraintVariableMappedToComplexTerm() {
    PartialProof pp = setupProof("sum1(z) = 0 + sum1(z) | z < 0");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.TOPLEFT;
    Rule rule = pp.getContext().getRule("O1");
    Variable x = pp.getContext().getRenaming("O1").getVariable("x");
    Substitution subst = TermFactory.createEmptySubstitution();
    Renaming eqnaming = pp.getProofState().getTopEquation().getRenaming();
    Term complexterm = CoraInputReader.readTerm("z + 0", eqnaming, _trs);
    subst.extend(x, complexterm);
    ConstrainedReductionHelper crh =
      new ConstrainedReductionHelper(rule.queryLeftSide(), rule.queryRightSide(),
        rule.queryConstraint(), pp.getContext().getRenaming("O1"), pos, subst, "XXX");
    MySmtSolver solver = new MySmtSolver(true);
    assertFalse(crh.checkConstraintGoodForReduction(
      pp.getProofState().getTopEquation().getEquation().getConstraint(), eqnaming, o, solver));
    assertTrue(solver._question == null);
    assertTrue(module.toString().equals("The XXX does not apply: constraint variable x is " +
      "instantiated by z + 0, which is not a value, nor a variable in the constraint of the " +
      "equation.\n\n"));
  }
}

