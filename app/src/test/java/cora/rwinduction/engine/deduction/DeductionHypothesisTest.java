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

import charlie.exceptions.CustomParserException;
import charlie.util.FixedList;
import charlie.terms.position.Position;
import charlie.terms.*;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.SmtProblem;
import charlie.smt.SmtSolver;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class DeductionHypothesisTest {
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
      "iter(x, i, z) -> iter(x, i+1, z+i) | i <= x\n");
  }

  private EquationContext readEquationContext(TRS trs, String leftgr, String lhs, String rhs,
                                              String constraint, String rightgr) {
    Renaming renaming = new Renaming(trs.queryFunctionSymbolNames());
    Term lg = CoraInputReader.readTermAndUpdateNaming(leftgr, renaming, trs);
    Term ls = CoraInputReader.readTermAndUpdateNaming(lhs, renaming, trs);
    Term rs = CoraInputReader.readTermAndUpdateNaming(rhs, renaming, trs);
    Term co = CoraInputReader.readTermAndUpdateNaming(constraint, renaming, trs);
    Term rg = CoraInputReader.readTermAndUpdateNaming(rightgr, renaming, trs);
    return new EquationContext(lg, new Equation(ls, rs, co), rg, 19, renaming);
  }

  private Renaming makeNaming(TRS trs, List<Term> lst) {
    TermPrinter printer = new TermPrinter(trs.queryFunctionSymbolNames());
    return printer.generateUniqueNaming(lst);
  }

  private void addHypothesis(PartialProof proof, String hypodesc) {
    TRS trs = proof.getContext().getTRS();
    var pair = EquationParser.parseEquation(hypodesc, trs);
    Hypothesis hypo = new Hypothesis(pair.fst(), 8, pair.snd());
    ProofState state = proof.getProofState().addHypothesis(hypo);
    proof.addProofStep(state, DeductionInduct.createStep(proof, Optional.empty()).get());
  }

  private PartialProof setupProof(String eqdesc, String hypodesc) {
    TRS trs = setupTRS();
    var pair = EquationParser.parseEquation(eqdesc, trs);
    PartialProof pp = new PartialProof(trs, FixedList.of(new EquationContext(pair.fst(), 19,
      pair.snd())), lst -> makeNaming(trs, lst));
    addHypothesis(pp, hypodesc);
    return pp;
  }

  private class MySmtSolver implements SmtSolver {
    private boolean _answer;
    String _question;
    public MySmtSolver(boolean answer) { _answer = answer; _question = null; }
    public Answer checkSatisfiability(SmtProblem problem) { assertTrue(false); return null; }
    public boolean checkValidity(SmtProblem prob) { _question = prob.toString(); return _answer; }
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
  public void testSuccessfulStepWithoutExtraTerms() {
    PartialProof pp = setupProof("sum1(x) = sum2(x) | x > 0", "sum1(z) = iter(z, 0, 0) | z ≥ 0");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    DeductionHypothesis step = DeductionHypothesis.createStep(pp, Optional.of(module), h8, false,
                            EquationPosition.TOPLEFT, TermFactory.createEmptySubstitution()).get();
    assertTrue(step.commandDescription().equals("hypothesis H8 L with [z := x]"));
    assertTrue(module.toString().equals(""));
    MySmtSolver solver = new MySmtSolver(true);
    Settings.smtSolver = solver;
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(module.toString().equals(""));
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getHypotheses().size() == 1);
    assertTrue(pp.getProofState().getOrderingRequirements().size() == 0);
    assertTrue(pp.getProofState().getEquations().get(0).toString().equals(
      "E20: (• , iter(x, 0, 0) ≈ sum2(x) | x > 0 , •)"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply HYPOTHESIS to E19 with induction hypothesis H8 " +
      "and substitution [z := x].  This does not cause any new ordering requirements to be " +
      "imposed.\n\n"));
    assertTrue(solver._question.equals("(0 >= i1) or (i1 >= 0)\n"));
  }

  @Test
  public void testSuccessfulStepWithExtraTerms() throws CustomParserException {
    PartialProof pp = setupProof("sum2(y)", "sum2(x)", "0 + sum1(x)", "y = x + 1 ∧ x > 0",
      "sum1(y)", "sum1(z) = iter(z, 0, y) | z ≥ 0");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    Substitution subst = TermFactory.createEmptySubstitution();
    subst.extend(pp.getProofState().getHypotheses().get(0).getRenamingCopy().getVariable("y"),
                 TheoryFactory.createValue(0));
    DeductionHypothesis step = DeductionHypothesis.createStep(pp, Optional.of(module), h8, false,
                            EquationPosition.parse("R2"), subst).get();
    assertTrue(step.commandDescription().equals("hypothesis H8 R2 with [y := 0, z := x]"));
    assertTrue(module.toString().equals(""));
    Settings.smtSolver = new MySmtSolver(true);
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(module.toString().equals(""));
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getHypotheses().size() == 1);
    assertTrue(pp.getProofState().getOrderingRequirements().size() == 2);
    assertTrue(pp.getProofState().getEquations().get(0).toString().equals(
      "E20: (sum2(y) , sum2(x) ≈ 0 + iter(x, 0, 0) | y = x + 1 ∧ x > 0 , sum1(y))"));
    assertTrue(pp.getProofState().getOrderingRequirements().get(0).toString().equals(
      "sum1(y) ≻ sum1(x) | y = x + 1 ∧ x > 0"));
    assertTrue(pp.getProofState().getOrderingRequirements().get(1).toString().equals(
      "sum1(y) ≻ iter(x, 0, 0) | y = x + 1 ∧ x > 0"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply HYPOTHESIS to E19 with induction hypothesis H8 " +
      "and substitution [y := 0, z := x].  To this end, we impose the requirements that " +
      "sum1(y) ≻ sum1(x) | y = x + 1 ∧ x > 0 and " +
      "sum1(y) ≻ iter(x, 0, 0) | y = x + 1 ∧ x > 0.\n\n"));
  }

  @Test
  public void testSuccessfulInverseStepWithoutExtraTerms() {
    PartialProof pp = setupProof("sum1(x) = sum2(x) | x > 0", "iter(z, a, 0) = sum2(z)| z ≥ 0");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    Substitution subst = TermFactory.createEmptySubstitution();
    subst.extend(pp.getProofState().getHypotheses().get(0).getRenamingCopy().getVariable("a"),
                 TheoryFactory.createValue(1));
    DeductionHypothesis step = DeductionHypothesis.createStep(pp, Optional.of(module), h8, true,
                            EquationPosition.TOPRIGHT, subst).get();
    assertTrue(step.commandDescription().equals("hypothesis H8^{-1} R with [a := 1, z := x]"));
    Settings.smtSolver = new MySmtSolver(true);
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(pp.getProofState().getOrderingRequirements().size() == 0);
    assertTrue(pp.getProofState().getEquations().get(0).toString().equals(
      "E20: (• , sum1(x) ≈ iter(x, 1, 0) | x > 0 , •)"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply HYPOTHESIS to E19 with induction hypothesis " +
      "H8^{-1} and substitution [a := 1, z := x].  This does not cause any new ordering " +
      "requirements to be imposed.\n\n"));
  }

  @Test
  public void testSuccessfulInverseStepWithExtraTerms() throws CustomParserException {
    PartialProof pp = setupProof("sum1(z)", "sum1(sum1(x))", "0 + sum1(x)", "x = x",
      "sum1(y)", "iter(z, 0, y) = sum1(y) | z ≥ 0");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    Substitution subst = TermFactory.createEmptySubstitution();
    subst.extend(pp.getProofState().getHypotheses().get(0).getRenamingCopy().getVariable("z"),
                 TheoryFactory.createValue(12));
    DeductionHypothesis step = DeductionHypothesis.createStep(pp, Optional.of(module), h8, true,
                            EquationPosition.parse("L1"), subst).get();
    assertTrue(step.commandDescription().equals("hypothesis H8^{-1} L1 with [y := x, z := 12]"));
    Settings.smtSolver = new MySmtSolver(true);
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(pp.getProofState().getOrderingRequirements().size() == 2);
    assertTrue(pp.getProofState().getEquations().get(0).toString().equals(
      "E20: (sum1(z) , sum1(iter(12, 0, x)) ≈ 0 + sum1(x) | x = x , sum1(y))"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply HYPOTHESIS to E19 with induction hypothesis " +
      "H8^{-1} and substitution [y := x, z := 12].  To this end, we impose the requirements that " +
      "sum1(z) ≻ sum1(x) | x = x and sum1(z) ≻ iter(12, 0, x) | x = x.\n\n"));
  }

  @Test
  public void testSuccessfulStepWithEqualLeftGreaterTerm() throws CustomParserException {
    PartialProof pp = setupProof("sum1(x)", "sum1(sum1(x))", "0 + sum1(x)", "x = x",
      "sum1(y)", "iter(z, 0, y) = sum1(y) | z ≥ 0");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    Substitution subst = TermFactory.createEmptySubstitution();
    subst.extend(pp.getProofState().getHypotheses().get(0).getRenamingCopy().getVariable("z"),
                 TheoryFactory.createValue(12));
    DeductionHypothesis step = DeductionHypothesis.createStep(pp, Optional.of(module), h8, true,
                            EquationPosition.parse("L1"), subst).get();
    assertTrue(step.commandDescription().equals("hypothesis H8^{-1} L1 with [y := x, z := 12]"));
    Settings.smtSolver = new MySmtSolver(true);
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(pp.getProofState().getOrderingRequirements().size() == 2);
    assertTrue(pp.getProofState().getEquations().get(0).toString().equals(
      "E20: (sum1(y) , sum1(iter(12, 0, x)) ≈ 0 + sum1(x) | x = x , sum1(y))"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply HYPOTHESIS to E19 with induction hypothesis " +
      "H8^{-1} and substitution [y := x, z := 12].  To this end, we impose the requirements that " +
      "sum1(y) ≻ sum1(x) | x = x and sum1(y) ≻ iter(12, 0, x) | x = x.\n\n"));
  }

  @Test
  public void testSuccessfulStepWithEqualRightGreaterTerm() throws CustomParserException {
    PartialProof pp = setupProof("sum2(sum2(y))", "0 + sum1(x)", "sum1(sum1(x))", "x < y",
      "sum1(x)", "sum1(y) = iter(z, 0, y) | z > 0");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    Substitution subst = TermFactory.createEmptySubstitution();
    subst.extend(pp.getProofState().getHypotheses().get(0).getRenamingCopy().getVariable("z"),
                 TheoryFactory.createValue(7));
    DeductionHypothesis step = DeductionHypothesis.createStep(pp, Optional.of(module), h8, false,
                            EquationPosition.parse("R1"), subst).get();
    assertTrue(step.commandDescription().equals("hypothesis H8 R1 with [y := x, z := 7]"));
    Settings.smtSolver = new MySmtSolver(true);
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(pp.getProofState().getOrderingRequirements().size() == 2);
    assertTrue(pp.getProofState().getEquations().get(0).toString().equals(
      "E20: (sum2(sum2(y)) , 0 + sum1(x) ≈ sum1(iter(7, 0, x)) | x < y , sum2(sum2(y)))"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply HYPOTHESIS to E19 with induction hypothesis " +
      "H8 and substitution [y := x, z := 7].  To this end, we impose the requirements that " +
      "sum2(sum2(y)) ≻ sum1(x) | x < y and sum2(sum2(y)) ≻ iter(7, 0, x) | x < y.\n\n"));
  }

  @Test
  public void testSuccessfulFinishingStep() throws CustomParserException {
     PartialProof pp = setupProof("sum1(x)", "sum1(sum1(x))", "sum1(iter(12, 0, x))", "x = x",
      "sum2(y)", "iter(z, 0, y) = sum1(y) | z ≥ 0");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    Substitution subst = TermFactory.createEmptySubstitution();
    subst.extend(pp.getProofState().getHypotheses().get(0).getRenamingCopy().getVariable("z"),
                 TheoryFactory.createValue(12));
    DeductionHypothesis step = DeductionHypothesis.createStep(pp, Optional.of(module), h8, true,
                            EquationPosition.parse("L1"), subst).get();
    assertTrue(step.commandDescription().equals("hypothesis H8^{-1} L1 with [y := x, z := 12]"));
    assertTrue(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(pp.getProofState().getOrderingRequirements().size() == 2);
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getEquations().get(0).toString().equals(
      "E20: (sum2(y) , sum1(iter(12, 0, x)) ≈ sum1(iter(12, 0, x)) | x = x , sum2(y))"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply HYPOTHESIS to E19 with induction hypothesis " +
      "H8^{-1} and substitution [y := x, z := 12].  To this end, we impose the requirements that " +
      "sum2(y) ≻ sum1(x) | x = x and sum2(y) ≻ iter(12, 0, x) | x = x.\n\n"));
  }

  @Test
  public void testNoSuitableInductionHypothesis() {
    PartialProof pp = setupProof("sum1(x)", "sum1(x)", "sum2(x)", "x > 0", "sum2(x)",
      "sum1(x) = sum2(x) | x ≥ 0");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    Substitution subst = TermFactory.createEmptySubstitution();
    assertTrue(DeductionHypothesis.createStep(pp, Optional.of(module), h8, false,
                                              EquationPosition.TOPLEFT, subst).isEmpty());
    assertTrue(module.toString().equals("The hypothesis cannot be applied, as it would cause an " +
      "obviously unsatisfiable ordering requirement to be imposed.\n\n"));
  }

  @Test
  public void testHypothesisDoesNotMatch() {
    PartialProof pp = setupProof("sum1(x) = sum2(x) | x > 0", "sum1(sum1(x)) = sum2(z)| z ≥ 0");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(DeductionHypothesis.createStep(pp, Optional.of(module), h8, false,
                       EquationPosition.TOPLEFT, TermFactory.createEmptySubstitution()).isEmpty());
    assertTrue(module.toString().equals("The induction hypothesis does not apply: x does not " +
      "instantiate sum1(x) (not an application).\n\n"));
  }

  @Test
  public void testHypothesisDoesNotMatchInverse() {
    PartialProof pp = setupProof("sum1(x) = sum2(x) | x > 0", "sum1(z) = sum2(z)| z ≥ 0");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(DeductionHypothesis.createStep(pp, Optional.of(module), h8, true,
                       EquationPosition.TOPLEFT, TermFactory.createEmptySubstitution()).isEmpty());
    assertTrue(module.toString().equals("The induction hypothesis does not apply: constant sum2 " +
      "is not instantiated by sum1.\n\n"));
  }

  @Test
  public void testConstraintNotSatisfied() {
    PartialProof pp = setupProof("sum1(x) = sum2(x) | x > 0", "sum1(z) = sum2(z)| z ≥ 0");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    DeductionHypothesis step = DeductionHypothesis.createStep(pp, Optional.of(module), h8, true,
                           EquationPosition.TOPRIGHT, TermFactory.createEmptySubstitution()).get();
    assertTrue(module.toString().equals(""));
    Settings.smtSolver = new MySmtSolver(false);
    assertFalse(step.verifyAndExecute(pp, Optional.of(module)));
    assertTrue(module.toString().equals("The induction hypothesis does not apply: I could not " +
      "prove that x > 0 ⊨ x ≥ 0.\n\n"));
  }

  @Test
  public void testCreateStepWithExtraVariables() throws CustomParserException {
    PartialProof pp = setupProof("sum2(y)", "sum2(x)", "0 + sum1(x)", "y = x + 1 ∧ x > 0",
      "sum1(y)", "sum1(z) = iter(z, 0, y) | z ≥ a");
    Hypothesis h8 = pp.getProofState().getHypothesisByName("H8");
    OutputModule module = OutputModule.createUnitTestModule();
    Substitution subst = TermFactory.createEmptySubstitution();
    assertTrue(DeductionHypothesis.createStep(pp, Optional.of(module), h8, false,
                            EquationPosition.parse("R2"), subst).isEmpty());
    assertTrue(subst.domain().size() == 0);
    assertTrue(module.toString().equals("Not enough information given: I could not determine " +
      "the substitution to be used for y, a.\n\n"));
  }
}

