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
import charlie.terms.Term;
import charlie.terms.TermPrinter;
import charlie.terms.Renaming;
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

class DeductionInductTest {
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

  public PartialProof setupProof(String leftgr, String left, String right, String constr,
                                 String rightgr) {
    TRS trs = setupTRS();
    Renaming renaming = new Renaming(trs.queryFunctionSymbolNames());
    Optional<Term> lg, rg;
    if (leftgr == null) lg = Optional.empty();
    else lg = Optional.of(CoraInputReader.readTermAndUpdateNaming(leftgr, renaming, trs));
    Term le = CoraInputReader.readTermAndUpdateNaming(left, renaming, trs);
    Term ri = CoraInputReader.readTermAndUpdateNaming(right, renaming, trs);
    Term co = CoraInputReader.readTermAndUpdateNaming(constr, renaming, trs);
    if (rightgr == null) rg = Optional.empty();
    else rg = Optional.of(CoraInputReader.readTermAndUpdateNaming(rightgr, renaming, trs));
    TermPrinter printer = new TermPrinter(Set.of());
    return new PartialProof(trs,
      FixedList.of(new EquationContext(lg, new Equation(le, ri, co), rg, 11, renaming)),
      lst -> printer.generateUniqueNaming(lst));
  }

  @Test
  public void testInductWithNoLeftOrRight() {
    PartialProof pp = setupProof(null, "sum1(x)", "iter(x, 0, 0)", "x >= 0", null);
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionInduct step = DeductionInduct.createStep(pp, o).get();
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getTopEquation().getIndex() == 12);
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E12: (sum1(x) , sum1(x) ≈ iter(x, 0, 0) | x ≥ 0 , iter(x, 0, 0))"));
    assertTrue(pp.getProofState().getHypotheses().size() == 1);
    assertTrue(pp.getProofState().getHypotheses().get(0).toString().equals(
      "H11: sum1(x) ≈ iter(x, 0, 0) | x ≥ 0"));
    assertTrue(pp.getProofState().getOrderingRequirements().size() == 0);
    assertTrue(pp.getCommandHistory().size() == 1);
    assertTrue(pp.getCommandHistory().get(0).equals("induct"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals(
      "We apply INDUCT to E11: (• , sum1(x) ≈ iter(x, 0, 0) | x ≥ 0 , •), which does not " +
      "impose any new ordering requirements but simply adds sum1(x) ≈ iter(x, 0, 0) | x ≥ 0 " +
      "to the set H of induction hypotheses.\n\n"));
  }

  @Test
  public void testInductWithEqualLeftAndRight() {
    PartialProof pp = setupProof("sum1(x)", "sum1(x)", "iter(x, 0, 0)", "x >= 0", "iter(x, 0, 0)");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionInduct step = DeductionInduct.createStep(pp, o).get();
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getTopEquation().getIndex() == 11);
    assertTrue(pp.getProofState().getHypotheses().size() == 1);
    assertTrue(pp.getProofState().getHypotheses().get(0).toString().equals(
      "H11: sum1(x) ≈ iter(x, 0, 0) | x ≥ 0"));
    assertTrue(pp.getProofState().getOrderingRequirements().size() == 0);
    assertTrue(pp.getCommandHistory().size() == 1);
    assertTrue(pp.getCommandHistory().get(0).equals("induct"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals(
      "We apply INDUCT to E11: (sum1(x) , sum1(x) ≈ iter(x, 0, 0) | x ≥ 0 , iter(x, 0, 0)), " +
      "which does not impose any new ordering requirements but simply adds " +
      "sum1(x) ≈ iter(x, 0, 0) | x ≥ 0 to the set H of induction hypotheses.\n\n"));
  }

  @Test
  public void testInductWithDifferentLeftAndRight() {
    PartialProof pp = setupProof("sum1(x+1)", "sum1(x)", "iter(x, 1, 0)", "x >= 0", "iter(x, 0, 0)");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionInduct step = DeductionInduct.createStep(pp, o).get();
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E12: (sum1(x) , sum1(x) ≈ iter(x, 1, 0) | x ≥ 0 , iter(x, 1, 0))"));
    assertTrue(pp.getProofState().getHypotheses().size() == 1);
    assertTrue(pp.getProofState().getHypotheses().get(0).toString().equals(
      "H11: sum1(x) ≈ iter(x, 1, 0) | x ≥ 0"));
    assertTrue(pp.getProofState().getOrderingRequirements().size() == 2);
    assertTrue(pp.getProofState().getOrderingRequirements().get(0).toString().equals(
      "sum1(x + 1) ≽ sum1(x) | x ≥ 0"));
    assertTrue(pp.getProofState().getOrderingRequirements().get(1).toString().equals(
      "iter(x, 0, 0) ≽ iter(x, 1, 0) | x ≥ 0"));
    assertTrue(pp.getCommandHistory().size() == 1);
    assertTrue(pp.getCommandHistory().get(0).equals("induct"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals(
      "We apply INDUCT to E11: (sum1(x + 1) , sum1(x) ≈ iter(x, 1, 0) | x ≥ 0 , iter(x, 0, 0)), " +
      "which adds the equation into H, and imposes the ordering requirements " +
      "sum1(x + 1) ≽ sum1(x) | x ≥ 0 and iter(x, 0, 0) ≽ iter(x, 1, 0) | x ≥ 0.\n\n"));
  }

  @Test
  public void testInductWithOnlyDifferentLeft() {
    PartialProof pp = setupProof("sum1(x+1)", "sum1(x)", "iter(x,0,0)", "x >= 0", "iter(x,0,0)");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionInduct step = DeductionInduct.createStep(pp, o).get();
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E12: (sum1(x) , sum1(x) ≈ iter(x, 0, 0) | x ≥ 0 , iter(x, 0, 0))"));
    assertTrue(pp.getProofState().getHypotheses().size() == 1);
    assertTrue(pp.getProofState().getOrderingRequirements().size() == 1);
    assertTrue(pp.getProofState().getOrderingRequirements().get(0).toString().equals(
      "sum1(x + 1) ≽ sum1(x) | x ≥ 0"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals(
      "We apply INDUCT to E11: (sum1(x + 1) , sum1(x) ≈ iter(x, 0, 0) | x ≥ 0 , iter(x, 0, 0)), " +
      "which adds the equation into H, and imposes the ordering requirement " +
      "sum1(x + 1) ≽ sum1(x) | x ≥ 0.\n\n"));
  }
}

