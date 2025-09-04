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

import charlie.util.Pair;
import charlie.util.FixedList;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.*;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.Valuation;
import charlie.smt.SmtProblem;
import charlie.smt.SmtSolver;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class DeductionDisproveTest {
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
      "nil :: list\n" +
      "cons :: Int -> list -> list\n" +
      "append :: list -> list -> list\n" +
      "append(nil, ys) -> ys\n" +
      "append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n");
  }

  public PartialProof setupProof(String left, String right, String constr) {
    TRS trs = setupTRS();
    MutableRenaming renaming = new MutableRenaming(trs.queryFunctionSymbolNames());
    Term le = CoraInputReader.readTermAndUpdateNaming(left, renaming, trs);
    Term ri = CoraInputReader.readTermAndUpdateNaming(right, renaming, trs);
    Term co = CoraInputReader.readTermAndUpdateNaming(constr, renaming, trs);
    TermPrinter printer = new TermPrinter(Set.of());
    return new PartialProof(trs,
      FixedList.of(new EquationContext(new Equation(le, ri, co), 11, renaming)),
      lst -> printer.generateUniqueNaming(lst));
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
  public void testFirstOrderTheory() {
    PartialProof pp = setupProof("4", "y + 1", "y > 2 ∧ y < 5");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionDisprove step = DeductionDisprove.createStep(pp, o);
    Valuation val = new Valuation();
    val.setInt(1, 4);
    MySmtSolver solver = new MySmtSolver(new MySmtSolver.Answer.YES(val));
    Settings.smtSolver = solver;
    step.explain(module);
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(solver._storage.equals("(i1 >= 3) and (4 >= i1) and (3 # i1)\n"));
    assertTrue(pp.getProofState().isFinalState());
    assertTrue(pp.getProofState().isContradictionState());
    assertTrue(step.commandDescription().equals("disprove"));
    step.explain(module);
    // the explanation before and after verify are not the same
    assertTrue(module.toString().equals(
      "We apply DISPROVE to E11, which succeeds because the constraint y > 2 ∧ y < 5 ∧ " +
      "¬(4 = y + 1) is satisfiable.\n\n" +
      "We apply DISPROVE to E11, which succeeds because under the substitution [y := 4], " +
      "the constraint y > 2 ∧ y < 5 evaluates to true, while the sides of the equation can be " +
      "calculated to 4 and 5 respectively.\n\n"));

  }
}

