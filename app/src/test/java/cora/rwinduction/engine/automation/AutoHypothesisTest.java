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
import cora.rwinduction.engine.deduction.DeductionHypothesis;

class AutoHypothesisTest {
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
      "sum3 :: Int -> Int\n" +
      "sum3(x) -> 1 | x < 2\n" +
      "sum3(x) -> sum3(x - 1) + x | x >= 2\n" +
      "nil :: list\n" +
      "cons :: Int -> list -> list\n" +
      "append :: list -> list -> list\n" +
      "append(nil, x) -> x\n" +
      "append(cons(x, y), z) -> cons(x, append(y, z))\n");
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
  public void testBestSide() {
    TRS trs = setupTRS();
    // both sides have a bounding term of TOP ==> just pick the left
    var pair = EquationParser.parseEquation("sum1(x) = sum2(x)", trs);
    EquationContext ec = new EquationContext(pair.fst(), 3, pair.snd());
    assertTrue(AutoHypothesis.chooseBestSide(trs, ec) == EquationPosition.Side.Left);
    // one side has a defined symbol, the other has a constructor symbol or calculation symbol
    assertTrue(AutoHypothesis.chooseBestSide(trs, readEquationContext(trs, "append(x,y)",
      "append(x,y)", "cons(3,y)", "true", "cons(5,y)")) == EquationPosition.Side.Left);
    assertTrue(AutoHypothesis.chooseBestSide(trs, readEquationContext(trs, "sum1(x) + y",
      "sum1(x)", "sum2(x)", "true", "sum2(x)")) == EquationPosition.Side.Right);
    // one has a constructor symbol, the other a calculation symbol
    assertTrue(AutoHypothesis.chooseBestSide(trs, readEquationContext(trs, "x + 3",
      "sum1(x)", "sum2(x)", "x > 0", "cons(x, nil)")) == EquationPosition.Side.Right);
    // one side has a calculation symbol, the other a variable
    assertTrue(AutoHypothesis.chooseBestSide(trs, readEquationContext(trs, "x + 3",
      "sum1(x)", "sum2(x)", "x > 0", "x")) == EquationPosition.Side.Left);
    // both sides have the same ==> pick the one where the bound term is not equal to the main term
    assertTrue(AutoHypothesis.chooseBestSide(trs, readEquationContext(trs, "sum1(x)",
      "sum1(x)", "sum2(x)", "x > 0", "sum2(sum2(x))")) == EquationPosition.Side.Right);
    assertTrue(AutoHypothesis.chooseBestSide(trs, readEquationContext(trs, "cons(x, cons(3, y))",
      "nil", "nil", "x > 0", "nil")) == EquationPosition.Side.Left);
  }

  private PartialProof complexProof() {
    PartialProof pp = setupProof(
      "cons(3, nil)",               // left bounding term, headed by a constructor
      "sum2(a) + 1",                // lhs of the equation
      "sum1(iter(a, b, sum2(x)))",  // rhs of the equation
      "b > 5",                      // constraint of the equation
      "iter(a, b, x + 1)",          // right bouding term, headed by a defined symbol
      "iter(a, b - 1, c + 1) = iter(a, b, c) | b > 0");
    addHypothesis(pp, "sum1(x) = sum2(x) + 1 | 1 = 1", 2);
    addHypothesis(pp, "sum1(x) = sum3(x) | x > 0", 3);
    return pp;
  }

  @Test
  public void testPossibleSteps() {
    PartialProof pp = complexProof();
    OutputModule module = OutputModule.createUnitTestModule();
    Settings.setStrategy(Settings.Strategy.Full);
    // first option
    Settings.smtSolver = new FixedAnswerValidityChecker(true);
    assertTrue(AutoHypothesis.createHypothesisStep(pp, module).commandDescription().equals(
      "hypothesis H1^{-1} r1 with [a := a, b := b, c := sum2(x)]"));
    // second option
    Settings.smtSolver = new FixedAnswerValidityChecker(false, true);
    assertTrue(AutoHypothesis.createHypothesisStep(pp, module).commandDescription().equals(
      "hypothesis H2 r with [x := iter(a, b, sum2(x))]"));
    // third option (NOT H3, because x is not instantiated by a variable)
    Settings.smtSolver = new FixedAnswerValidityChecker(false, false, true);
    assertTrue(AutoHypothesis.createHypothesisStep(pp, module).commandDescription().equals(
      "hypothesis H2^{-1} l with [x := a]"));
    // nothing applies
    Settings.smtSolver = new FixedAnswerValidityChecker(false, false, false, true);
    assertTrue(AutoHypothesis.createHypothesisStep(pp, module) == null);
  }

  @Test
  public void testCannotChooseSteps() {
    PartialProof pp = complexProof();
    addHypothesis(pp, "sum1(x) = sum3(x)", 4);
    OutputModule module = OutputModule.createUnitTestModule();
    Settings.setStrategy(Settings.Strategy.Full);
    Settings.smtSolver = new FixedAnswerValidityChecker(false, true);
    assertTrue(AutoHypothesis.createHypothesisStep(pp, module) == null);
    assertTrue(module.toString().equals(
      "There are multiple possible induction hypothesis steps, and it is not obvious " +
      "which to choose from the following:\n\n" +
      "  * hypothesis H2 r with [x := iter(a, b, sum2(x))]\n" +
      "  * hypothesis H4 r with [x := iter(a, b, sum2(x))]\n\n"));
  }

  @Test
  public void testChooseLaterOption() {
    PartialProof pp = complexProof();
    addHypothesis(pp, "iter(a, b - 1, c + 1) + 7 = iter(a, b, c) | a = 0", 4);
    OutputModule module = OutputModule.createUnitTestModule();
    Settings.setStrategy(Settings.Strategy.Full);
    Settings.smtSolver = new FixedAnswerValidityChecker(true, true, true);
    assertTrue(AutoHypothesis.createHypothesisStep(pp, module).commandDescription().equals(
      "hypothesis H2 r with [x := iter(a, b, sum2(x))]"));
  }
}

