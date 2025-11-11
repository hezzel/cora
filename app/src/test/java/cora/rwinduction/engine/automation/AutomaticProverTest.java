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
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.Optional;

import charlie.util.FixedList;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.*;
import charlie.trs.TRS;
import charlie.smt.Valuation;
import charlie.smt.SmtSolver.Answer;
import charlie.smt.ProgrammableSmtSolver;
import charlie.reader.CoraInputReader;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;
import cora.rwinduction.engine.deduction.DeductionInduct;

class AutomaticProverTest {
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
      "nil :: List\n" +
      "cons :: Int -> List -> List\n"
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

  /* ========== TESTS ========== */

  @Test
  public void testCategoriseFirstOrderTheory() {
    Valuation val = new Valuation();
    val.setInt(1, 4);
    Settings.smtSolver =
      new ProgrammableSmtSolver("(i1 >= 3) and (3 >= i1) and (3 # i1)", new Answer.NO(),
                                "(i1 >= 3) and (4 >= i1) and (3 # i1)", new Answer.MAYBE("meh"),
                                "(i1 >= 3) and (5 >= i1) and (3 # i1)", new Answer.YES(val));
    PartialProof pp = setupProof("3 = x", "sum1(x) = sum2(x)");
    EquationContext ec = pp.getProofState().getTopEquation();
    MutableRenaming renaming = ec.getRenaming().copy();
    Term left = ec.getLhs();
    Term right = ec.getRhs();
    TRS trs = pp.getContext().getTRS();
    Optional<OutputModule> empty = Optional.empty();

    // constraint forces 3 = x
    Term constr = CoraInputReader.readTerm("x > 2 ∧ x < 4", renaming, trs);
    DeductionStep step = AutomaticProver.categorise(left, right, constr, Optional.of(left),
       Optional.of(right), pp.getProofState(), pp.getContext(), true).createStep(pp, empty);
    assertTrue(step.commandDescription().equals("eq-delete"));

    // SMT-solver cannot determine if constraint forces 3 = x
    constr = CoraInputReader.readTerm("x > 2 ∧ x < 5", renaming, trs);
    assertTrue(AutomaticProver.categorise(left, right, constr, Optional.empty(),
      Optional.of(right), pp.getProofState(), pp.getContext(), false) == null);

    // SMT-solver does not force 3 = x, so even for an incomplete case, we get a disprove!
    constr = CoraInputReader.readTerm("x > 2 ∧ x < 6", renaming, trs);
    step = AutomaticProver.categorise(left, right, constr, Optional.of(left), Optional.empty(),
       pp.getProofState(), pp.getContext(), true).createStep(pp, empty);
    assertTrue(step.commandDescription().equals("disprove theory with [x := 4]"));
  }

  @Test
  public void testCategoriseHigherOrderTheory() {
    Valuation val = new Valuation();
    val.setInt(1, 37);
    val.setInt(2, 42);
    val.setInt(3, 0);
    Settings.smtSolver =
      new ProgrammableSmtSolver("(i1 = i2) and (i1 # i2)", new Answer.NO(),
                                "true and (i1 # i2)", new Answer.YES(val),
                                "i1 + i2 # i1 + i3", new Answer.YES(val));

    // F(x) = F(y) | x = y
    PartialProof pp = setupProof("{ F :: Int -> Int} F(x) = F(y) | x = y", "sum1(x) = sum2(x)");
    EquationContext ec = pp.getProofState().getTopEquation();
    Term left = ec.getLhs();
    Term right = ec.getRhs();
    Optional<OutputModule> empty = Optional.empty();

    // constraint forces x = y
    Term constr = ec.getConstraint();
    DeductionStep step = AutomaticProver.categorise(left, right, constr, Optional.empty(),
       Optional.empty(), pp.getProofState(), pp.getContext(), true).createStep(pp, empty);
    assertTrue(step.commandDescription().equals("eq-delete"));

    // constraint does not force x = y; note that this requires an explicit disprove-search, so the
    // completeness flag should matter!
    constr = CoraInputReader.readTerm("true", pp.getContext().getTRS());
    assertTrue(AutomaticProver.categorise(left, right, constr, Optional.empty(), Optional.empty(),
      pp.getProofState(), pp.getContext(), true) == null);
    step = AutomaticProver.categorise(left, right, constr, Optional.empty(), Optional.empty(),
       pp.getProofState(), pp.getContext(), false).createStep(pp, empty);
    assertTrue(step.commandDescription().equals(
      "disprove theory with [F := [+](37), x := 42, y := 0]"));
  }

  @Test
  public void testCategoriseHdelete() {
    Settings.smtSolver = new ProgrammableSmtSolver();
    PartialProof pp = setupProof("sum1(sum1(x)) = sum1(sum2(x))", "sum2(z) = sum1(z)");
    EquationContext ec = pp.getProofState().getTopEquation();
    DeductionStep step = AutomaticProver.categorise(ec.getLhs(), ec.getRhs(), ec.getConstraint(),
      Optional.empty(), Optional.of(ec.getRhs()), pp.getProofState(), pp.getContext(),
      true).createStep(pp, Optional.empty());
    assertTrue(step.commandDescription().equals("hdelete H1^{-1} l1 with [z := x]"));
  }

  @Test
  public void testCategoriseCheapDisprove() {
    Settings.smtSolver = new ProgrammableSmtSolver();
    PartialProof pp = setupProof("nil = cons(x, y)", "sum2(z) = sum1(z)");
    EquationContext ec = pp.getProofState().getTopEquation();
    DeductionStep step = AutomaticProver.categorise(ec.getLhs(), ec.getRhs(), ec.getConstraint(),
      Optional.empty(), Optional.of(ec.getRhs()), pp.getProofState(), pp.getContext(),
      true).createStep(pp, Optional.empty());
    assertTrue(step.commandDescription().equals("disprove root"));
  }
}

