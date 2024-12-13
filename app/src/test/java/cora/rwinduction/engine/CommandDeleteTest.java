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

package cora.rwinduction.engine;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;
import java.util.Set;

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
import cora.rwinduction.parser.ExtendedTermParser;

class CommandDeleteTest {
  private Equation _defaultEquation = null;

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
    Equation eq1 = ExtendedTermParser.parseEquation("sum1(x) = sum2(x) | x ≥ 0", trs);
    Equation eq2 = ExtendedTermParser.parseEquation(eqdesc, trs);
    _defaultEquation = eq1;
    return new PartialProof(trs, FixedList.of(eq1, eq2), new TermPrinter(Set.of()));
  }

  private void testDeleteEquation(String eqdesc) {
    PartialProof pp = setupProof(eqdesc);
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Command cmd = new CommandDelete();
    cmd.run(pp, module);
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getTopEquation() == _defaultEquation);
    assertTrue(pp.getProofState().getHypotheses().size() == 0);
    assertTrue(pp.getCommandHistory().size() == 1);
    assertTrue(pp.getCommandHistory().get(0).equals("delete"));
    assertTrue(module.toString().equals(""));
  }

  private String testFailToDeleteEquation(String eqdesc) {
    PartialProof pp = setupProof(eqdesc);
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Command cmd = new CommandDelete();
    cmd.run(pp, module);
    assertTrue(pp.getProofState().getEquations().size() == 2);
    assertTrue(pp.getCommandHistory().size() == 0);
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
      "are not the same, and the constraint is satisfiable using substitution [x:=4, y:=3].\n\n"));
  }
}

