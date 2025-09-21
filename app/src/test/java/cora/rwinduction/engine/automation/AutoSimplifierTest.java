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

package cora.rwinduction.engine.automation;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;
import java.util.Set;
import java.util.Optional;

import charlie.terms.position.PositionFormatException;
import charlie.terms.position.Position;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.Renaming;
import charlie.terms.*;
import charlie.substitution.MutableSubstitution;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.Truth;
import charlie.smt.SmtProblem;
import charlie.smt.SmtSolver;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class AutoSimplifierTest {
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
      "append(nil, z) -> z\n" +
      "append(cons(x, y), z) -> cons(x, append(y, z))\n");
  }

  public PartialProof setupProof(String eqdesc) {
    TRS trs = setupTRS();
    TermPrinter printer = new TermPrinter(trs.queryFunctionSymbolNames());
    return new PartialProof(trs, EquationParser.parseEquationList(eqdesc, trs),
                            lst -> printer.generateUniqueNaming(lst));
  }

  @Test
  public void testFindSimplificationWithoutSmt() {
    PartialProof pp = setupProof("append(append(nil, x), cons(y, z)) = append(cons(y, x), z)");
    DeductionStep step = AutoSimplifier.createSingleStep(pp);
    assertTrue(step.commandDescription().equals("simplify O6 L1 with [z := x]"));
    Optional<OutputModule> o = Optional.of(OutputModule.createUnitTestModule());
    assertTrue(step.execute(pp, o));
    step = AutoSimplifier.createSingleStep(pp);
    assertTrue(step.commandDescription().equals("simplify O7 R with [x := y, y := x, z := z]"));
  }

  /**
   * Smt solver to be used for a single SMT validity check, which is then replaced by the next
   * solver in the settings.
   */
  private class ReplacingSmtSolver implements SmtSolver {
    private boolean _answer;
    String _question;
    private SmtSolver _next;

    public ReplacingSmtSolver(boolean answer, SmtSolver next) {
      _answer = answer;
      _question = null;
      _next = next;
    }

    public Answer checkSatisfiability(SmtProblem problem) {
      assertTrue(false);
      return null;
    }

    public boolean checkValidity(SmtProblem problem) {
      _question = problem.toString();
      Settings.smtSolver = _next;
      return _answer;
    }
  }

  @Test
  public void testFindSimplificationWithSmt() {
    PartialProof pp = setupProof("sum1(x) = sum1(y) | x < 3 ∧ y > 0");
    ReplacingSmtSolver solver4 = new ReplacingSmtSolver(true, null);
    ReplacingSmtSolver solver3 = new ReplacingSmtSolver(false, solver4);
    ReplacingSmtSolver solver2 = new ReplacingSmtSolver(false, solver3);
    ReplacingSmtSolver solver1 = new ReplacingSmtSolver(false, solver2);
    Settings.smtSolver = solver1;
    DeductionStep step = AutoSimplifier.createSingleStep(pp);
    assertTrue(solver1._question.equals("(i1 >= 3) or (0 >= i2) or (0 >= i1)\n"));
    assertTrue(solver2._question.equals("(i1 >= 3) or (0 >= i2) or (i1 >= 1)\n"));
    assertTrue(solver3._question.equals("(i1 >= 3) or (0 >= i2) or (0 >= i2)\n"));
    assertTrue(solver4._question.equals("(i1 >= 3) or (0 >= i2) or (i2 >= 1)\n"));
    assertTrue(step.commandDescription().equals("simplify O2 R with [x := y]"));
  }
}

