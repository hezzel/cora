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
import java.util.Set;

import charlie.util.Pair;
import charlie.types.TypeFactory;
import charlie.terms.replaceable.Renaming;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.Valuation;
import charlie.smt.SmtProblem;
import charlie.smt.SmtSolver;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class DeductionAlterConstraintTest {
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
      "f :: (Int -> Int) -> unit -> Int\n" +
      "f(F, x) -> 0\n");
  }

  public PartialProof setupProof(String eqdesc) {
    TRS trs = setupTRS();
    TermPrinter printer = new TermPrinter(Set.of());
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
  public void testPureEquivalence() {
    PartialProof pp = setupProof("iter(x, i, z) = iter(i, z, x) | x > i ∧ z != 0");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term newc = CoraInputReader.readTerm("(z > 0 ∨ z < 0) ∧ i <= x - 1", renaming,
                                         pp.getContext().getTRS());
    DeductionAlterGeneraliseConstraint dac =
      DeductionAlterGeneraliseConstraint.createAlterStep(pp, o, newc);
    assertTrue(dac.commandDescription().equals(
      "alter constraint (z > 0 \\/ z < 0) /\\ i <= x - 1"));
    MySmtSolver mysolver = new MySmtSolver(true);
    Settings.smtSolver = mysolver;
    assertTrue(dac.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getTopEquation().getIndex() == 2);
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , iter(x, i, z) ≈ iter(i, z, x) | (z > 0 ∨ z < 0) ∧ i ≤ x - 1 , •)"));
    assertTrue(module.toString().equals(""));
    dac.explain(module);
    assertTrue(module.toString().equals(
      "We apply ALTER to replace the constraint of E1 by (z > 0 ∨ z < 0) ∧ i ≤ x - 1.\n\n"));
    assertTrue(mysolver._question.equals(
      // x ≤ i ∨ z = 0 ∨ ( (z ≥ 1 ∨ z + 1 ≤ 0) ∧ i + 1 ≤ x )
      "(i2 >= i1) or (i3 = 0) or (((i3 >= 1) or (0 >= 1 + i3)) and (i1 >= 1 + i2))\n" +
      // ( z ≤ 0 ∧ z ≥ 0 ) ∨ i ≥ x ∨ ( x ≥ i + 1 ∧ z != 0 )
      "((0 >= i3) and (i3 >= 0)) or (i2 >= i1) or ((i1 >= 1 + i2) and (i3 # 0))\n"));
  }

  @Test
  public void testNonEquivalence() {
    PartialProof pp = setupProof("iter(x, i, z) = iter(i, z, x) | x > i ∧ z != 0");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term newc = CoraInputReader.readTerm("z != 0", renaming, pp.getContext().getTRS());
    DeductionAlterGeneraliseConstraint dac =
      DeductionAlterGeneraliseConstraint.createAlterStep(pp, o, newc);
    MySmtSolver mysolver = new MySmtSolver(false);
    Settings.smtSolver = mysolver;
    assertFalse(dac.verify(o));
    assertTrue(module.toString().equals("It is not obvious if this usage of alter is " +
      "permitted: I could not prove that x > i ∧ z ≠ 0 ⟺  z ≠ 0.\n\n"));
  }

  @Test
  public void testGeneralise() {
    PartialProof pp = setupProof("iter(x, i, z) = iter(i, z, x) | x > i");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term newc = CoraInputReader.readTerm("x >= i", renaming, pp.getContext().getTRS());
    DeductionAlterGeneraliseConstraint dac =
      DeductionAlterGeneraliseConstraint.createGeneraliseStep(pp, o, newc);
    Settings.smtSolver = new MySmtSolver(false);
    assertFalse(dac.verify(o));
    dac.explain(module);
    assertTrue(module.toString().equals("It is not obvious if this usage of generalise is " +
      "permitted: I could not prove that x > i ⇒ x ≥ i.\n\n" +
      "We apply GENERALISE to replace the constraint of E1 by x ≥ i.\n\n"));

    MySmtSolver mysolver = new MySmtSolver(true);
    Settings.smtSolver = mysolver;
    assertTrue(dac.verifyAndExecute(pp, o));
    assertTrue(mysolver._question.equals("(i2 >= i1) or (i1 >= i2)\n"));
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getTopEquation().getIndex() == 2);
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , iter(x, i, z) ≈ iter(i, z, x) | x ≥ i , •)"));
  }

  @Test
  public void testFreshVariable() {
    PartialProof pp = setupProof("iter(x, i, z) = iter(i, z, x) | x > i ∧ z != 0");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term newc = CoraInputReader.readTerm("x > i ∧ z != y", renaming, pp.getContext().getTRS());
    assertTrue(DeductionAlterGeneraliseConstraint.createGeneraliseStep(pp, o, newc) == null);
    assertTrue(module.toString().equals("Fresh occurrence of y is not allowed in this " +
      "application of the GENERALISE command (use ALTER ADD to add new variables to the " +
      "constraint).\n\n"));
  }
}

