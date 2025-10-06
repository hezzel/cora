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

package cora.rwinduction.engine.automation;

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
import cora.rwinduction.engine.deduction.DeductionInduct;

class AutoDeleterTest {
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

  private void addHypothesis(PartialProof proof, String hypodesc, int index) {
    TRS trs = proof.getContext().getTRS();
    var pair = EquationParser.parseEquation(hypodesc, trs);
    Hypothesis hypo = new Hypothesis(pair.fst(), index, pair.snd());
    ProofState state = proof.getProofState().addHypothesis(hypo);
    proof.addProofStep(state, DeductionInduct.createStep(proof, Optional.empty()));
  }

  private PartialProof setupProof(String eqdesc, String hypodesc) {
    TRS trs = setupTRS();
    var pair = EquationParser.parseEquation(eqdesc, trs);
    PartialProof pp = new PartialProof(trs, FixedList.of(new EquationContext(pair.fst(), 19,
      pair.snd())), lst -> makeNaming(trs, lst));
    addHypothesis(pp, hypodesc, 1);
    return pp;
  }

  private PartialProof setupProof(String leftgr, String lhs, String rhs, String constr,
                                  String rightgr, String hypodesc) {
    TRS trs = setupTRS();
    PartialProof pp = new PartialProof(trs, FixedList.of(readEquationContext(trs, leftgr, lhs,
      rhs, constr, rightgr)), lst -> makeNaming(trs, lst));
    addHypothesis(pp, hypodesc, 1);
    return pp;
  }

  /* ========== TESTS ========== */

  @Test
  public void testMatchInSubterm() {
    PartialProof pp = setupProof(
      "sum1(iter(x, sum2(y1), z)) = sum1(iter(x, sum1(y2), z)) | y1 + 1 = y2 + 1",
      "iter(a, sum2(b), c) = iter(a, sum1(d), c) | b = d");
    addHypothesis(pp, "sum1(iter(x, y, z)) = sum1(iter(x, y, u)) | z = u + 1", 2);
    addHypothesis(pp, "sum2(x) = sum1(y) | x = y + 1", 3);
    OutputModule module = OutputModule.createUnitTestModule();
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(false, true, true);
    Settings.smtSolver = solver;
    DeductionStep step = AutoDeleter.createHdeleteStep(pp, Optional.of(module));
    assertTrue(step.toString().equals("hdelete H1 l1 with [a := x, b := y1, c := z, d := y2]"));
    assertTrue(solver.queryNumberQuestions() == 2);
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(solver.queryNumberQuestions() == 3);
    assertTrue(module.toString().equals(""));
    assertTrue(pp.getProofState().isFinalState());
    assertTrue(pp.getProofState().getHypotheses().size() == 3);
    assertTrue(pp.getProofState().getOrderingRequirements().size() == 0);
    assertTrue(solver.queryQuestion(0).equals("(i1 # i2) or (i1 = 1 + i2)\n"));
    assertTrue(solver.queryQuestion(1).equals("(i1 # i2) or (i1 = i2)\n")); // y1 = y2 => y1 = y2
  }

  @Test
  public void testMatchInHead() {
    PartialProof pp = setupProof("sum1(x) = sum2(x)", "sum1 = sum2");
    Settings.smtSolver = null;
    DeductionStep step = AutoDeleter.createHdeleteStep(pp, Optional.empty());
    assertTrue(step.toString().equals("hdelete H1 l.*1 with []"));
  }

  @Test
  public void testMatchReverseHypothesis() {
    PartialProof pp = setupProof("sum1(sum1(x)) = sum1(sum1(y)) | x = z + 1 ∧ z = y + 1",
      "sum1(b) = sum1(a) | c = b + 1 ∧ a = c + 1");
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(true);
    Settings.smtSolver = solver;
    DeductionStep step = AutoDeleter.createHdeleteStep(pp, Optional.empty());
    assertTrue(step.toString().equals("hdelete H1^{-1} l1 with [a := x, b := y, c := z]"));
    assertTrue(solver.queryNumberQuestions() == 1);
    assertTrue(solver.queryQuestion(0).equals(
      "(i1 # 1 + i2) or (i2 # 1 + i3) or ((i2 = 1 + i3) and (i1 = 1 + i2))\n"));
  }

  @Test
  public void testMatchVariableHypothesis() {
    PartialProof pp = setupProof("sum1(q) = sum1(iter(2, a, q)) | a < 0",
      "{z :: Int} z = iter(x, i, z) | x > i");
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(true);
    Settings.smtSolver = solver;
    DeductionStep step = AutoDeleter.createHdeleteStep(pp, Optional.empty());
    assertTrue(step.toString().equals("hdelete H1 l1 with [i := a, x := 2, z := q]"));
    assertTrue(solver.queryNumberQuestions() == 1);
    assertTrue(solver.queryQuestion(0).equals("(i1 >= 0) or (1 >= i1)\n"));
  }

  @Test
  public void testNoMatchingHypothesis() {
    PartialProof pp = setupProof("sum1 = sum2", "sum1(x) = sum2(x)");
    Settings.smtSolver = null;
    OutputModule module = OutputModule.createUnitTestModule();
    DeductionStep step = AutoDeleter.createHdeleteStep(pp, Optional.of(module));
    assertTrue(step == null);
    assertTrue(module.toString().equals("There is no applicable position where we can clearly " +
      "apply HDELETE with any available induction hypothesis.\n\n"));
  }

  @Test
  public void testBoundingTermsSameAsEquation() {
    PartialProof pp = setupProof("iter(sum1(x), y, z)", "iter(sum1(x), y, z)",
      "iter(sum2(x), y, z)", "x > 0", "iter(sum2(x), y, z)", "sum1 = sum2");
    Settings.smtSolver = null;
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(AutoDeleter.createHdeleteStep(pp, Optional.of(module)) == null);
    assertTrue(module.toString().equals("No HDELETE step can be applied, because the bounding " +
      "terms of the equation context are both equal to the corresponding side of the " +
      "equation.  Hence, there is no way to apply HDELETE that would not lead to an " +
      "unsatisfiable ordering requirement.\n\n"));
  }

  @Test
  public void testDeletionShouldBeUsedInstead() {
    PartialProof pp = setupProof("sum1(sum2(x)) = sum1(sum2(x))", "sum2(x) = sum2(x)");
    Settings.smtSolver = null;
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(AutoDeleter.createHdeleteStep(pp, Optional.of(module)) == null);
    assertTrue(module.toString().equals("The left- and right-hand side of the equation are the " +
      "same.  Use DELETE instead!\n\n"));
  }

}

