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
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.Truth;
import charlie.smt.SmtProblem;
import charlie.smt.SmtSolver;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class DeductionSimplifyTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "sum1 :: Int -> Int\n" +
      "sum1(x) -> 0 | x <= 0\n" +
      "sum1(x) -> x + sum1(x-1) | x > 0\n" +
      "sum2 :: Int -> Int\n" +
      "sum2(x) -> iter(x, 0, 0)\n" +
      "iter :: Int -> Int -> Int -> Int\n" +
      "iter(x, i, z) -> z | i > x\n" +
      "iter(x, i, z) -> iter(x, i+1, z+i) | i <= x\n" +
      "input :: Int\n" +
      "input -> x | y > 0\n" +
      "tmp :: Int -> Int\n" +
      "tmp(x) -> 0\n" +
      "sum3 :: Int -> Int\n" +
      "sum3(x) -> iter(x, i, z) | c0 = 0 ∧ c1 = 0 ∧ i = c0 ∧ z = c1\n");
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

  private class MySimpleSolver implements SmtSolver {
    public Answer checkSatisfiability(SmtProblem problem) { assertTrue(false); return null; }
    public boolean checkValidity(SmtProblem prob) {
      return prob.queryCombinedConstraint().simplify() instanceof Truth;
    }
  }

  @Test
  public void testCreateStep() throws CustomParserException {
    PartialProof pp = setupProof("sum1(z) + 0 = iter(z, 0, 0) | z < 0");
    OutputModule module = OutputModule.createUnitTestModule();
    MySmtSolver solver = new MySmtSolver(true);
    Settings.smtSolver = solver;
    EquationPosition pos = new EquationPosition(EquationPosition.Side.Left, Position.parse("1"));
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "O2", pos,
                                                 TermFactory.createEmptySubstitution()).get();
    assertTrue(step.commandDescription().equals("simplify O2 L1 with [x := z]"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply SIMPLIFICATION to E1 with rule O2 and " +
      "substitution [x := z].\n\n"));
    assertTrue(solver._question == null); // it doesn't get called when just creating the step
  }

  @Test
  public void testStepImmutable() {
    PartialProof pp = setupProof("sum1(z) = iter(z, 0, 0) | z >= 0");
    OutputModule module = OutputModule.createUnitTestModule();
    Substitution empty = TermFactory.createEmptySubstitution();
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "O4",
                                                          EquationPosition.TOPRIGHT, empty).get();
    empty.extend(TermFactory.createVar("u", CoraInputReader.readType("Int")),
                 TheoryFactory.createValue(5));
    assertTrue(step.commandDescription().equals("simplify O4 R with [i := 0, x := z, z := 0]"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply SIMPLIFICATION to E1 with rule O4 and " +
      "substitution [i := 0, x := z, z := 0].\n\n"));
  }

  @Test
  public void testSimplifyUnconstrained() {
    PartialProof pp = setupProof("sum1(x) = sum2(x) | x > 0");
    OutputModule module = OutputModule.createUnitTestModule();
    MySmtSolver solver = new MySmtSolver(true);
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "O3",
                       EquationPosition.TOPRIGHT, TermFactory.createEmptySubstitution()).get();
    assertTrue(step.verify(Optional.of(module)));
    assertTrue(step.execute(pp, Optional.of(module)));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , sum1(x) ≈ iter(x, 0, 0) | x > 0 , •)"));
    assertTrue(pp.getDeductionHistory().get(0) == step);
    assertTrue(solver._question == null); // it doesn't get called for unconstrained rules
    assertTrue(module.toString().equals(""));
  }

  @Test
  public void testSimplifyConstrained() throws CustomParserException {
    PartialProof pp = setupProof("sum1(z) + 0 = iter(z, 0, 0) | z > 0");
    OutputModule module = OutputModule.createUnitTestModule();
    MySmtSolver solver = new MySmtSolver(true);
    Settings.smtSolver = solver;
    EquationPosition pos = new EquationPosition(EquationPosition.Side.Left, Position.parse("1"));
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "O2", pos,
                                                 TermFactory.createEmptySubstitution()).get();
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , z + sum1(z - 1) + 0 ≈ iter(z, 0, 0) | z > 0 , •)"));
    assertTrue(solver._question.equals("(0 >= i1) or (i1 >= 1)\n"));
    assertTrue(module.toString().equals(""));
  }

  @Test
  public void testSimplifyWithSubstitution() {
    PartialProof pp = setupProof("input = 7");
    OutputModule module = OutputModule.createUnitTestModule();
    Settings.smtSolver = new MySimpleSolver();

    Substitution subst = TermFactory.createEmptySubstitution();
    Variable x = pp.getContext().getRenaming("O6").getVariable("x");
    Variable y = pp.getContext().getRenaming("O6").getVariable("y");
    subst.extend(x, TheoryFactory.createValue(-1));
    subst.extend(y, TheoryFactory.createValue(8));

    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "O6",
                                                          EquationPosition.TOPLEFT, subst).get();
    assertTrue(step.verify(Optional.of(module)));
    assertTrue(step.execute(pp, Optional.of(module)));
    assertTrue(pp.getProofState().getTopEquation().toString().equals("E2: (• , -1 ≈ 7 , •)"));
    assertTrue(pp.getCommandHistory().get(0).equals("simplify O6 L with [x := -1, y := 8]"));
    assertTrue(module.toString().equals(""));
  }

  @Test
  public void testSimplifyWithSubstitutionMappingToConstraintVar() {
    PartialProof pp = setupProof("input = 7 | z = 7");
    OutputModule module = OutputModule.createUnitTestModule();
    Settings.smtSolver = new MySimpleSolver();
    Renaming rulenaming = pp.getContext().getRenaming("O6");
    Renaming eqnaming = pp.getProofState().getTopEquation().getRenamingCopy();

    Substitution subst = TermFactory.createEmptySubstitution();
    Variable x = rulenaming.getVariable("x");
    Variable y = rulenaming.getVariable("y");
    subst.extend(x, eqnaming.getVariable("z"));
    subst.extend(y, TheoryFactory.createValue(1));

    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "O6",
                                                          EquationPosition.TOPLEFT, subst).get();
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(pp.getProofState().getTopEquation().toString().equals("E2: (• , z ≈ 7 | z = 7 , •)"));
    assertTrue(step.commandDescription().equals("simplify O6 L with [x := z, y := 1]"));
  }

  @Test
  public void testSimplifyNoMatch() {
    PartialProof pp = setupProof("sum1(x) = sum2(x) | x > 0");
    OutputModule module = OutputModule.createUnitTestModule();
    MySmtSolver solver = new MySmtSolver(true);
    Settings.smtSolver = solver;
    assertTrue(DeductionSimplify.createStep(pp, Optional.of(module), "O3", EquationPosition.TOPLEFT,
                                            TermFactory.createEmptySubstitution()).isEmpty());
    assertTrue(module.toString().equals(
      "The rule does not apply due to failed matching (matching debug info says constant sum2 " +
      "is not instantiated by sum1.)\n\n"));
  }

  @Test
  public void testSimplifyBadPosition() throws CustomParserException {
    PartialProof pp = setupProof("sum1(x) = sum2(x) | x > 0");
    OutputModule module = OutputModule.createUnitTestModule();
    MySmtSolver solver = new MySmtSolver(true);
    Settings.smtSolver = solver;
    EquationPosition pos = new EquationPosition(EquationPosition.Side.Left, Position.parse("1.2"));
    Substitution empty = TermFactory.createEmptySubstitution();
    assertTrue(DeductionSimplify.createStep(pp, Optional.of(module), "O3", pos, empty).isEmpty());
    assertTrue(module.toString().equals("No such position: L1.2.\n\n"));
  }

  @Test
  public void testMissingVariablesFromSubstitution() {
    PartialProof pp = setupProof("input = 7");
    OutputModule module = OutputModule.createUnitTestModule();
    MySmtSolver solver = new MySmtSolver(true);
    Settings.smtSolver = solver;
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "O6",
                  EquationPosition.TOPLEFT, TermFactory.createEmptySubstitution()).get();
    assertFalse(step.verify(Optional.of(module)));
    assertTrue(module.toString().equals(
      "Not enough information given: " +
      "I could not determine the substitution to be used for x, y.\n\n"));
    assertTrue(solver._question == null);
  }

  @Test
  public void testSimplifyConstraintVariableNotAValue() {
    PartialProof pp = setupProof("sum1(z + 1) = iter(z + 1, 0, 0) | z ≥ 0");
    OutputModule module = OutputModule.createUnitTestModule();
    MySmtSolver solver = new MySmtSolver(true);
    Settings.smtSolver = solver;
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "O2",
                  EquationPosition.TOPLEFT, TermFactory.createEmptySubstitution()).get();
    assertFalse(step.verify(Optional.of(module)));
    assertTrue(module.toString().equals("The rule does not apply: " +
      "constraint variable x is instantiated by z + 1, which is not a value, " +
      "nor a variable in the constraint of the equation.\n\n"));
    assertTrue(solver._question == null);
    // we CAN execute it even if we shouldn't, though!
    assertTrue(step.execute(pp, Optional.of(module)));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , z + 1 + sum1(z + 1 - 1) ≈ iter(z + 1, 0, 0) | z ≥ 0 , •)"));
  }

  @Test
  public void testSimplifyConstraintNotImplied() {
    PartialProof pp = setupProof("sum1(z) = iter(z, 0, 0) | z >= 0");
    OutputModule module = OutputModule.createUnitTestModule();
    Settings.smtSolver = new MySimpleSolver();
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "O2",
      EquationPosition.TOPLEFT, TermFactory.createEmptySubstitution()).get();
    assertFalse(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(module.toString().equals(
      "The rule does not apply: I could not prove that z ≥ 0 ⊨ z > 0.\n\n"));
    assertTrue(pp.getProofState() == step.getOriginalState());
  }

  @Test
  public void testOnlyNeededVariablesAfterSimplify() {
    PartialProof pp = setupProof("0 = tmp(z) | x < 0");
    OutputModule module = OutputModule.createUnitTestModule();
    MySmtSolver solver = new MySmtSolver(false);
    Settings.smtSolver = solver;
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "O7",
      EquationPosition.TOPRIGHT, TermFactory.createEmptySubstitution()).get();
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    EquationContext ec = pp.getProofState().getTopEquation();
    assertTrue(ec.toString().equals("E2: (• , 0 ≈ 0 | x < 0 , •)"));
    assertTrue(ec.getRenamingCopy().getReplaceable("z") == null);
  }
}

