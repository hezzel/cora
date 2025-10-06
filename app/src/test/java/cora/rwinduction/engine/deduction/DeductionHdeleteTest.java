/**************************************************************************************************
 Copyright 2025 Cynthia Kop

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

import charlie.util.FixedList;
import charlie.terms.position.PositionFormatException;
import charlie.terms.position.Position;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.*;
import charlie.substitution.MutableSubstitution;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.SmtProblem;
import charlie.smt.FixedAnswerValidityChecker;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class DeductionHdeleteTest {
  /* ========== SETUP ========== */

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
      "toint :: Bool -> Int\n" +
      "toint(false) -> 0\n" +
      "toint(true) -> 1\n"
    );
  }

  private EquationContext readEquationContext(TRS trs, String leftgr, String lhs, String rhs,
                                              String constraint, String rightgr) {
    MutableRenaming renaming = new MutableRenaming(trs.queryFunctionSymbolNames());
    Term lg = CoraInputReader.readTermAndUpdateNaming(leftgr, renaming, trs);
    Term ls = CoraInputReader.readTermAndUpdateNaming(lhs, renaming, trs);
    Term rs = CoraInputReader.readTermAndUpdateNaming(rhs, renaming, trs);
    Term co = CoraInputReader.readTermAndUpdateNaming(constraint, renaming, trs);
    Term rg = CoraInputReader.readTermAndUpdateNaming(rightgr, renaming, trs);
    return new EquationContext(lg, new Equation(ls, rs, co), rg, 19, renaming);
  }

  private MutableRenaming makeNaming(TRS trs, List<Term> lst) {
    TermPrinter printer = new TermPrinter(trs.queryFunctionSymbolNames());
    return printer.generateUniqueNaming(lst);
  }

  private void addHypothesis(PartialProof proof, String hypodesc) {
    TRS trs = proof.getContext().getTRS();
    var pair = EquationParser.parseEquation(hypodesc, trs);
    Hypothesis hypo = new Hypothesis(pair.fst(), 8, pair.snd());
    ProofState state = proof.getProofState().addHypothesis(hypo);
    proof.addProofStep(state, DeductionInduct.createStep(proof, Optional.empty()));
  }

  private PartialProof setupProof(String eqdesc, String hypodesc) {
    TRS trs = setupTRS();
    var pair = EquationParser.parseEquation(eqdesc, trs);
    PartialProof pp = new PartialProof(trs, FixedList.of(new EquationContext(pair.fst(), 19,
      pair.snd())), lst -> makeNaming(trs, lst));
    addHypothesis(pp, hypodesc);
    return pp;
  }

  private PartialProof setupProof(String leftgr, String lhs, String rhs, String constr,
                                  String rightgr, String hypodesc) {
    TRS trs = setupTRS();
    PartialProof pp = new PartialProof(trs, FixedList.of(readEquationContext(trs, leftgr, lhs,
      rhs, constr, rightgr)), lst -> makeNaming(trs, lst));
    addHypothesis(pp, hypodesc);
    return pp;
  }

  /* ========== TESTS ========== */

  @Test
  public void testSuccessfulStepAtRootWithTrivialSubstitution() {
    PartialProof pp = setupProof("sum1(x) = sum2(x) | x > 0", "sum2(y) = sum1(y) | y > 1");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    DeductionHdelete step = DeductionHdelete.createStep(pp, Optional.of(module), h8, true,
                            EquationPosition.TOPLEFT, new MutableSubstitution());
    assertTrue(step.commandDescription().equals("hdelete H8^{-1} l with [y := x]"));
    assertTrue(module.toString().equals(""));
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(true);
    Settings.smtSolver = solver;
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(module.toString().equals(""));
    assertTrue(pp.getProofState().isFinalState());
    assertTrue(pp.getProofState().getHypotheses().size() == 1);
    assertTrue(pp.getProofState().getOrderingRequirements().size() == 0);
    assertTrue(solver.queryQuestion(0).equals("(0 >= i1) or (i1 >= 2)\n")); // x > 0 => x > 1
  }

  @Test
  public void testFailedStepAtRoot() {
    PartialProof pp = setupProof("sum1(x) = sum2(x) | x > 0", "sum1(y) = iter(y, 1, 1) | y > 1");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(DeductionHdelete.createStep(pp, Optional.of(module), h8, false,
               EquationPosition.TOPLEFT, new MutableSubstitution()) == null);
    assertTrue(module.toString().equals(
      "The induction hypothesis does not match the right-hand side of the equation.\n\n"));
  }

  @Test
  public void testSuccessfulStepInContext() throws PositionFormatException {
    PartialProof pp = setupProof("sum1(x) + 13", "sum1(x) + 12", "sum2(y) + 12", "x = y",
      "sum2(y) + 13", "sum1(a) = sum2(b) | b >= a");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    DeductionHdelete step = DeductionHdelete.createStep(pp, Optional.of(module), h8, false,
                            EquationPosition.parse("l1"), new MutableSubstitution());
    assertTrue(step.commandDescription().equals("hdelete H8 l1 with [a := x, b := y]"));
    assertTrue(module.toString().equals(""));
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(true);
    Settings.smtSolver = solver;
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(module.toString().equals(""));
    assertTrue(pp.getProofState().isFinalState());
    assertTrue(pp.getProofState().getHypotheses().size() == 1);
    assertTrue(pp.getProofState().getOrderingRequirements().size() == 0);
  }

  @Test
  public void testFailedContextPositionDoesNotExist() throws PositionFormatException {
    PartialProof pp = setupProof("sum1(sum1(x))", "sum1(sum1(x))", "12 + sum2(y)", "x > y",
      "sum2(y) + 13", "sum1(a) = sum2(b) | b >= a");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(DeductionHdelete.createStep(pp, Optional.of(module), h8, true,
               EquationPosition.parse("r2"), new MutableSubstitution()) == null);
    assertTrue(module.toString().equals("The left-hand side of the equation does not have a " +
      "position 2.\n\n"));
  }

  @Test
  public void testFailedContextSubtermDoesNotMatch() throws PositionFormatException {
    PartialProof pp = setupProof("sum1(sum1(x))", "sum1(y) + 12", "12 + sum2(y)", "x > y",
      "sum2(y) + 13", "sum1(a) = sum2(b) | b >= a");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(DeductionHdelete.createStep(pp, Optional.of(module), h8, true,
               EquationPosition.parse("r2"), new MutableSubstitution()) == null);
    assertTrue(module.toString().equals("The induction hypothesis does not match the " +
      "left-hand side of the equation.\n\n"));
  }

  @Test
  public void testFailedContextDifferentContext() throws PositionFormatException {
    PartialProof pp = setupProof("sum1(sum1(x))", "13 + sum1(x)", "12 + sum2(y)", "x > y",
      "sum2(y) + 13", "sum1(a) = sum2(b) | b >= a");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(DeductionHdelete.createStep(pp, Optional.of(module), h8, true,
               EquationPosition.parse("r2"), new MutableSubstitution()) == null);
    assertTrue(module.toString().equals(
      "The two sides have different contexts: 13 + [] versus 12 + [].\n\n"));
  }

  @Test
  public void testFailedContextDifferentTypes() throws PositionFormatException {
    PartialProof pp = setupProof("toint(x) = sum2(sum1(y)) | x ∧ y = 1", "sum1(z) = z | z = 1");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(DeductionHdelete.createStep(pp, Optional.of(module), h8, false,
               EquationPosition.parse("r1"), new MutableSubstitution()) == null);
    assertTrue(module.toString().equals("The induction hypothesis does not match the " +
      "left-hand side of the equation.\n\n"));
  }

  @Test
  public void testContextAtPartialPosition() throws PositionFormatException {
    PartialProof pp = setupProof("sum2(x)", "3 + sum1(x)", "3 + iter(0, 0, x)","x = 0",
      "sum2(0)", "sum1 = iter(0,0)");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    DeductionHdelete step = DeductionHdelete.createStep(pp, Optional.of(module), h8, false,
               EquationPosition.parse("l2*1"), new MutableSubstitution());
    assertTrue(step.commandDescription().equals("hdelete H8 l2.*1 with []"));
    assertTrue(module.toString().equals(""));
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(true);
    Settings.smtSolver = solver;
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(module.toString().equals(""));
    assertTrue(pp.getProofState().isFinalState());
    assertTrue(pp.getProofState().getHypotheses().size() == 1);
    assertTrue(pp.getProofState().getOrderingRequirements().size() == 0);
  }

  @Test
  public void testContextFailsInPartialPosition() throws PositionFormatException {
    PartialProof pp = setupProof("x + sum1(1) = x + iter(0, 0, 2) | x = 0", "sum1 = iter(0,0)");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(DeductionHdelete.createStep(pp, Optional.of(module), h8, false,
               EquationPosition.parse("l2*1"), new MutableSubstitution()) == null);
    assertTrue(module.toString().equals(
      "The two sides have different contexts: x + [](1) versus x + [](2).\n\n"));
  }

  @Test
  public void testImpossibleOrderingRequirement() throws PositionFormatException {
    PartialProof pp = setupProof("sum1(x)", "sum1(x)", "sum2(x)", "x > 0", "sum2(x)",
      "sum1(x) = sum2(x)");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(DeductionHdelete.createStep(pp, Optional.of(module), h8, false,
               EquationPosition.TOPLEFT, new MutableSubstitution()) == null);
    assertTrue(module.toString().equals(
      "Cannot apply an induction hypothesis at position ε when both bounding terms are the same " +
      "as the equation terms.\n\n"));
  }

  @Test
  public void testPossibleOrderingRequirementDueToPartial() throws PositionFormatException {
    PartialProof pp = setupProof("sum1(x)", "sum1(x)", "sum2(x)", "x > 0", "sum2(x)",
      "sum1 = sum2");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    DeductionHdelete step = DeductionHdelete.createStep(pp, Optional.of(module), h8, false,
               EquationPosition.parse("*1"), new MutableSubstitution());
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(module.toString().equals(""));
    assertTrue(pp.getProofState().isFinalState());
    assertTrue(pp.getProofState().getOrderingRequirements().size() == 0);
  }

  @Test
  public void testFigureOutFreshVariablesOnOtherSide() throws PositionFormatException {
    PartialProof pp = setupProof("iter(0, 0, sum1(x)) = iter(0, 0, sum2(y)) | x = z ∧ z = y",
                                 "sum2(b) = sum1(a) | a = c ∧ c = b");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    DeductionHdelete step = DeductionHdelete.createStep(pp, Optional.of(module), h8, true,
               EquationPosition.parse("l3"), new MutableSubstitution());
    assertTrue(step.commandDescription().equals(
      "hdelete H8^{-1} l3 with [a := x, b := y, c := z]"));
  }

  @Test
  public void testFreshVariablesDontQuiteMatch() throws PositionFormatException {
    PartialProof pp = setupProof("iter(0, 0, sum1(2+x)) = iter(0, 0, sum2(y+2))",
                                 "sum1(z+a) = sum2(a+z) | z > 0");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(DeductionHdelete.createStep(pp, Optional.of(module), h8, false,
               EquationPosition.parse("l3"), new MutableSubstitution()) == null);
    assertTrue(module.toString().equals(
      "The induction hypothesis does not match the right-hand side of the equation.\n\n"));
  }

  @Test
  public void testUnknowableVariablesInConstraint() throws PositionFormatException {
    PartialProof pp = setupProof("iter(0, 0, sum1(x)) = iter(0, 0, sum2(y)) | x = y",
                                 "sum2(b) = sum1(a) | a ≥ c ∧ c ≥ b");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    DeductionHdelete step = DeductionHdelete.createStep(pp, Optional.of(module), h8, true,
               EquationPosition.parse("l3"), new MutableSubstitution());
    Settings.smtSolver = new FixedAnswerValidityChecker(false);
    assertFalse(step.verify(Optional.of(module)));
    assertTrue(module.toString().equals("The induction hypothesis does not apply: " +
      "constraint variable c is not mapped to anything.\n\n"));
  }

  @Test
  public void testSupplySubstitution() throws PositionFormatException {
    PartialProof pp = setupProof("iter(0, 0, sum1(x)) = iter(0, 0, sum2(y)) | x = y",
                                 "sum1(b) = sum2(a) | a ≥ c ∧ c ≥ b");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(h8.getRenaming().getReplaceable("c"),
      (Variable)pp.getProofState().getTopEquation().getRenaming().getReplaceable("y"));
    DeductionHdelete step = DeductionHdelete.createStep(pp, Optional.of(module), h8, false,
                                                        EquationPosition.parse("l3"), subst);
    assertTrue(step.commandDescription().equals("hdelete H8 l3 with [a := y, b := x, c := y]"));
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(true);
    Settings.smtSolver = solver;
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(module.toString().equals(""));
    assertTrue(solver.queryQuestion(0).equals("(i1 # i2) or ((i2 >= i2) and (i2 >= i1))\n"));
  }
}

