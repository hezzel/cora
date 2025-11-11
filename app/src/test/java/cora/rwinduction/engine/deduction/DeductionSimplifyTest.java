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

import charlie.terms.position.PositionFormatException;
import charlie.terms.position.Position;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.Renaming;
import charlie.terms.*;
import charlie.substitution.MutableSubstitution;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.Truth;
import charlie.smt.SmtProblem;
import charlie.smt.SmtSolver;
import charlie.smt.FixedAnswerValidityChecker;
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
      "sum3(x) -> iter(x, i, z) | c0 = 0 ∧ c1 = 0 ∧ i = c0 ∧ z = c1\n" +
      "pointless :: Int -> Int -> Int\n" +
      "pointless(x, y) -> pointless(x+y, y-1) | y > 0 ∧ x = x");
  }

  public PartialProof setupProof(String eqdesc) {
    TRS trs = setupTRS();
    TermPrinter printer = new TermPrinter(trs.queryFunctionSymbolNames());
    return new PartialProof(trs, EquationParser.parseEquationList(eqdesc, trs),
                            lst -> printer.generateUniqueNaming(lst));
  }

  private class MySimpleSolver implements SmtSolver {
    public Answer checkSatisfiability(SmtProblem problem) { assertTrue(false); return null; }
    public boolean checkValidity(SmtProblem prob) {
      return prob.queryCombinedConstraint().simplify() instanceof Truth;
    }
  }

  @Test
  public void testCreateStep() throws PositionFormatException {
    PartialProof pp = setupProof("sum1(z) + 0 = iter(z, 0, 0) | z < 0");
    OutputModule module = OutputModule.createUnitTestModule();
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker();
    Settings.smtSolver = solver;
    EquationPosition pos = new EquationPosition(EquationPosition.Side.Left, Position.parse("1"));
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "R2", pos,
                                                 new MutableSubstitution());
    assertTrue(step.commandDescription().equals("simplify R2 l1 with [x := z]"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply SIMPLIFICATION to E1 with rule R2 and " +
      "substitution [x := z].\n\n"));
    // it doesn't get called when just creating the step
    assertTrue(solver.queryNumberQuestions() == 0);
  }

  @Test
  public void testStepImmutable() {
    PartialProof pp = setupProof("sum1(z) = iter(z, 0, 0) | z >= 0");
    OutputModule module = OutputModule.createUnitTestModule();
    MutableSubstitution empty = new MutableSubstitution();
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "R4",
                                                          EquationPosition.TOPRIGHT, empty);
    empty.extend(TermFactory.createVar("u", CoraInputReader.readType("Int")),
                 TheoryFactory.createValue(5));
    assertTrue(step.commandDescription().equals("simplify R4 r with [i := 0, x := z, z := 0]"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply SIMPLIFICATION to E1 with rule R4 and " +
      "substitution [i := 0, x := z, z := 0].\n\n"));
  }

  @Test
  public void testSimplifyUnconstrained() {
    PartialProof pp = setupProof("sum1(x) = sum2(x) | x > 0");
    OutputModule module = OutputModule.createUnitTestModule();
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker();
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "R3",
                       EquationPosition.TOPRIGHT, new MutableSubstitution());
    assertTrue(step.verify(Optional.of(module)));
    assertTrue(step.execute(pp, Optional.of(module)));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , sum1(x) ≈ iter(x, 0, 0) | x > 0 , •)"));
    assertTrue(pp.getDeductionHistory().get(0) == step);
    assertTrue(solver.queryNumberQuestions() == 0); // it doesn't get called for unconstrained rules
    assertTrue(module.toString().equals(""));
  }

  @Test
  public void testSimplifyConstrained() throws PositionFormatException {
    PartialProof pp = setupProof("sum1(z) + 0 = iter(z, 0, 0) | z > 0");
    OutputModule module = OutputModule.createUnitTestModule();
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(true);
    Settings.smtSolver = solver;
    EquationPosition pos = new EquationPosition(EquationPosition.Side.Left, Position.parse("1"));
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "R2", pos,
                                                 new MutableSubstitution());
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , z + sum1(z - 1) + 0 ≈ iter(z, 0, 0) | z > 0 , •)"));
    assertTrue(solver.queryQuestion(0).equals("(0 >= i1) or (i1 >= 1)"));
    assertTrue(module.toString().equals(""));
  }

  @Test
  public void testSimplifyWithSubstitution() {
    PartialProof pp = setupProof("input = 7");
    OutputModule module = OutputModule.createUnitTestModule();
    Settings.smtSolver = new MySimpleSolver();

    MutableSubstitution subst = new MutableSubstitution();
    Replaceable x = pp.getContext().getRenaming("R6").getReplaceable("x");
    Replaceable y = pp.getContext().getRenaming("R6").getReplaceable("y");
    subst.extend(x, TheoryFactory.createValue(-1));
    subst.extend(y, TheoryFactory.createValue(8));

    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "R6",
                                                          EquationPosition.TOPLEFT, subst);
    assertTrue(step.verify(Optional.of(module)));
    assertTrue(step.execute(pp, Optional.of(module)));
    assertTrue(pp.getProofState().getTopEquation().toString().equals("E2: (• , -1 ≈ 7 , •)"));
    assertTrue(pp.getCommandHistory().get(0).equals("simplify R6 l with [x := -1, y := 8]"));
    assertTrue(module.toString().equals(""));
  }

  @Test
  public void testSimplifyWithSubstitutionMappingToConstraintVar() {
    PartialProof pp = setupProof("input = 7 | z = 7");
    OutputModule module = OutputModule.createUnitTestModule();
    Settings.smtSolver = new MySimpleSolver();
    Renaming rulenaming = pp.getContext().getRenaming("R6");
    Renaming eqnaming = pp.getProofState().getTopEquation().getRenaming();

    MutableSubstitution subst = new MutableSubstitution();
    Replaceable x = rulenaming.getReplaceable("x");
    Replaceable y = rulenaming.getReplaceable("y");
    subst.extend(x, (Variable)eqnaming.getReplaceable("z"));
    subst.extend(y, TheoryFactory.createValue(1));

    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "R6",
                                                          EquationPosition.TOPLEFT, subst);
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(pp.getProofState().getTopEquation().toString().equals("E2: (• , z ≈ 7 | z = 7 , •)"));
    assertTrue(step.commandDescription().equals("simplify R6 l with [x := z, y := 1]"));
  }

  @Test
  public void testPointlessVariableInRuleConstraint() {
    PartialProof pp = setupProof("pointless(x, y) = x + y | y > 3");
    OutputModule module = OutputModule.createUnitTestModule();
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(true);
    Settings.smtSolver = solver;
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "R9",
                                                          EquationPosition.TOPLEFT,
                                                          new MutableSubstitution());
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(solver.queryQuestion(0).equals("(3 >= i1) or ((i1 >= 1) and (i2 = i2))"));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , pointless(x + y, y - 1) ≈ x + y | y > 3 , •)"));
  }

  @Test
  public void testSimplifyNoMatch() {
    PartialProof pp = setupProof("sum1(x) = sum2(x) | x > 0");
    OutputModule module = OutputModule.createUnitTestModule();
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(true);
    Settings.smtSolver = solver;
    assertTrue(DeductionSimplify.createStep(pp, Optional.of(module), "R3", EquationPosition.TOPLEFT,
                                            new MutableSubstitution()) == null);
    assertTrue(module.toString().equals(
      "The rule does not apply due to failed matching (matching debug info says: Constant sum2 " +
      "is not instantiated by sum1.)\n\n"));
  }

  @Test
  public void testSimplifyBadPosition() throws PositionFormatException {
    PartialProof pp = setupProof("sum1(x) = sum2(x) | x > 0");
    OutputModule module = OutputModule.createUnitTestModule();
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(true);
    Settings.smtSolver = solver;
    EquationPosition pos = new EquationPosition(EquationPosition.Side.Left, Position.parse("1.2"));
    MutableSubstitution empty = new MutableSubstitution();
    assertTrue(DeductionSimplify.createStep(pp, Optional.of(module), "R3", pos, empty) == null);
    assertTrue(module.toString().equals("No such position: l1.2.\n\n"));
  }

  @Test
  public void testMissingVariablesFromSubstitution() {
    PartialProof pp = setupProof("input = 7");
    OutputModule module = OutputModule.createUnitTestModule();
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker();
    Settings.smtSolver = solver;
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "R6",
                  EquationPosition.TOPLEFT, new MutableSubstitution());
    assertFalse(step.verify(Optional.of(module)));
    assertTrue(module.toString().equals(
      "Not enough information given: " +
      "I could not determine the substitution to be used for x, y.\n\n"));
    assertTrue(solver.queryNumberQuestions() == 0);
  }

  @Test
  public void testSimplifyConstraintVariableNotAValue() {
    Settings.setStrategy(Settings.Strategy.Full);
    PartialProof pp = setupProof("sum1(z + 1) = iter(z + 1, 0, 0) | z ≥ 0");
    OutputModule module = OutputModule.createUnitTestModule();
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(true);
    Settings.smtSolver = solver;
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "R2",
                  EquationPosition.TOPLEFT, new MutableSubstitution());
    assertFalse(step.verify(Optional.of(module)));
    assertTrue(module.toString().equals("The rule does not apply: " +
      "constraint variable x is instantiated by z + 1, which is not a value or variable.\n\n"));
    assertTrue(solver.queryNumberQuestions() == 0);
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
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "R2",
      EquationPosition.TOPLEFT, new MutableSubstitution());
    assertFalse(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(module.toString().equals(
      "The rule does not apply: I could not prove that z ≥ 0 ⊨ z > 0.\n\n"));
    assertTrue(pp.getProofState() == step.getOriginalState());
  }

  @Test
  public void testOnlyNeededVariablesAfterSimplify() {
    PartialProof pp = setupProof("0 = tmp(z) | x < 0");
    OutputModule module = OutputModule.createUnitTestModule();
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(false);
    Settings.smtSolver = solver;
    DeductionSimplify step = DeductionSimplify.createStep(pp, Optional.of(module), "R7",
      EquationPosition.TOPRIGHT, new MutableSubstitution());
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    EquationContext ec = pp.getProofState().getTopEquation();
    assertTrue(ec.toString().equals("E2: (• , 0 ≈ 0 | x < 0 , •)"));
    assertTrue(ec.getRenaming().getReplaceable("z") == null);
  }
}

