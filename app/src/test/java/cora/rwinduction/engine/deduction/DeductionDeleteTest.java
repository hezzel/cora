/**************************************************************************************************
 Copyright 2024 Cynthia Kop

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
import cora.io.DefaultOutputModule;
import cora.io.ParseableTermPrinter;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class DeductionDeleteTest {
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

  public PartialProof setupProof(String eqdesc) {
    TRS trs = setupTRS();
    return new PartialProof(trs,
      EquationParser.parseEquationList("sum1(x) = sum2(x) | x ≥ 0 ; " + eqdesc, trs),
      new TermPrinter(Set.of()));
  }

  private void testDeleteEquation(String eqdesc) {
    PartialProof pp = setupProof(eqdesc);
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionDelete step = DeductionDelete.createStep(pp, o).get();
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getTopEquation().getIndex() == 1);
    assertTrue(pp.getProofState().getHypotheses().size() == 0);
    assertTrue(pp.getCommandHistory().size() == 1);
    assertTrue(pp.getCommandHistory().get(0).equals("delete"));
    assertTrue(module.toString().equals(""));
  }

  private String testFailToDeleteEquation(String eqdesc) {
    PartialProof pp = setupProof(eqdesc);
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Optional<OutputModule> o = Optional.of(module);
    Optional<DeductionDelete> dd = DeductionDelete.createStep(pp, o);
    if (dd.isEmpty()) return module.toString();
    DeductionDelete step = dd.get();
    assertFalse(step.verify(o));
    // it also works without an output module!
    o = Optional.empty();
    step = DeductionDelete.createStep(pp, o).get();
    assertFalse(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getEquations().size() == 2);
    assertTrue(pp.getProofState().getTopEquation().getIndex() == 2);
    assertTrue(pp.getCommandHistory().size() == 0);
    // return the output created when we did use an output module
    return module.toString();
  }

  @Test
  public void testDeleteBecauseEqual() {
    testDeleteEquation("sum1(x) -><- sum1(x) | x = 0");
  }

  class MySmtSolver implements SmtSolver {
    Answer _answer;
    String _storage;
    MySmtSolver(Answer a) { _answer = a; _storage = null; }
    public Answer checkSatisfiability(SmtProblem problem) {
      _storage = problem.toString();
      return _answer;
    }
    public boolean checkValidity(SmtProblem problem) {
      _storage = "Validity: " + problem.toString();
      return _answer instanceof Answer.NO;
    }
  }

  @Test
  public void testDeleteBecauseUnsatisfiable() {
    MySmtSolver solver = new MySmtSolver(new SmtSolver.Answer.NO());
    Settings.smtSolver = solver;
    testDeleteEquation("sum1(x) -><- sum2(x) | x > 0 ∧ x < 0");
    assertTrue(solver._storage.equals("(i1 >= 1) and (0 >= 1 + i1)\n"));
  }

  @Test
  public void testOmitOutputModule() {
    MySmtSolver solver = new MySmtSolver(new SmtSolver.Answer.NO());
    Settings.smtSolver = solver;
    TRS trs = setupTRS();
    PartialProof pp = new PartialProof(trs,
      EquationParser.parseEquationList("sum1(x) = sum2(x) | x ≥ 0 ; " +
                                       "sum1(x) = sum1(x) | x > 0 ; " +
                                       "sum1(x) = sum2(x) | x > x", trs),
      new TermPrinter(Set.of()));
    Optional<OutputModule> oo = Optional.empty();
    DeductionDelete step = DeductionDelete.createStep(pp, oo).get();
    assertTrue(step.verifyAndExecute(pp, oo));
    step = DeductionDelete.createStep(pp, oo).get();
    assertTrue(step.verifyAndExecute(pp, oo));
    solver = new MySmtSolver(new SmtSolver.Answer.MAYBE("something"));
    Settings.smtSolver = solver;
    step = DeductionDelete.createStep(pp, oo).get();
    assertFalse(step.verify(oo));
    assertTrue(step.execute(pp, oo));
    assertTrue(pp.isDone());
  }

  @Test
  public void testNoDeleteBecauseMaybeSatisfiable() {
    MySmtSolver solver = new MySmtSolver(new SmtSolver.Answer.MAYBE("Solver doesn't know."));
    Settings.smtSolver = solver;
    String output = testFailToDeleteEquation("sum1(x) -><- sum2(x) | x > 0 ∧ x < 0");
    assertTrue(solver._storage.equals("(i1 >= 1) and (0 >= 1 + i1)\n"));
    assertTrue(output.equals("The DELETE rule is not obviously applicable: the left- and " +
      "right-hand side are not the same, and checking satisfiability returns MAYBE (Solver " +
      "doesn't know.)\n\n"));
  }

  @Test
  public void testNoDeleteBecauseSatisfiable() {
    Valuation val = new Valuation();
    val.setInt(1, 4);
    val.setInt(2, 3);
    MySmtSolver solver = new MySmtSolver(new SmtSolver.Answer.YES(val));
    Settings.smtSolver = solver;
    String output = testFailToDeleteEquation("sum1(x) -><- sum2(x) | x > y ∧ x ≤ y+1");
    assertTrue(solver._storage.equals("(i1 >= 1 + i2) and (1 + i2 >= i1)\n"));
    assertTrue(output.equals("The DELETE rule is not applicable: the left- and right-hand side " +
      "are not the same, and the constraint is satisfiable using substitution [x := 4, y := 3]." +
      "\n\n"));
  }

  @Test
  public void testHistory() {
    MySmtSolver solver = new MySmtSolver(new SmtSolver.Answer.NO());
    PartialProof pp = setupProof("sum1(x) -><- sum2(x) | x > 0 ∧ x < 0");
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionDelete step = DeductionDelete.createStep(pp, o).get();
    ParseableTermPrinter ptp = new ParseableTermPrinter(Set.of());
    assertTrue(step.commandDescription(ptp).equals("delete"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(solver._storage == null);
    assertTrue(module.toString().equals("We apply DELETION to E2 because the constraint is " +
      "unsatisfiable.  Thus, we may remove this equation from the proof state.\n\n"));
  }
}

