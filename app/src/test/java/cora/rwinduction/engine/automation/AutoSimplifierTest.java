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
import charlie.smt.FixedAnswerValidityChecker;
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
      "append(cons(x, y), z) -> cons(x, append(y, z))\n" +
      "suc :: Int -> Int\n" +
      "suc -> [+](1)\n" +
      "len :: list -> Int\n" +
      "len(nil) -> 0\n" +
      "len(cons(x,y)) -> 1 + len(y)\n");
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
    assertTrue(step.commandDescription().equals("simplify R6 l1 with [z := x]"));
    Optional<OutputModule> o = Optional.of(OutputModule.createUnitTestModule());
    assertTrue(step.execute(pp, o));
    step = AutoSimplifier.createSingleStep(pp);
    assertTrue(step.commandDescription().equals("simplify R7 r with [x := y, y := x, z := z]"));
  }

  @Test
  public void testFindSimplificationWithSmt() {
    PartialProof pp = setupProof("sum1(x) = sum1(y) | x < 3 ∧ y > 0");
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(false, false, false, true);
    Settings.smtSolver = solver;
    DeductionStep step = AutoSimplifier.createSingleStep(pp);
    assertTrue(solver.queryQuestion(0).equals("(i1 >= 3) or (0 >= i2) or (0 >= i1)\n"));
    assertTrue(solver.queryQuestion(1).equals("(i1 >= 3) or (0 >= i2) or (i1 >= 1)\n"));
    assertTrue(solver.queryQuestion(2).equals("(i1 >= 3) or (0 >= i2) or (0 >= i2)\n"));
    assertTrue(solver.queryQuestion(3).equals("(i1 >= 3) or (0 >= i2) or (i2 >= 1)\n"));
    assertTrue(step.commandDescription().equals("simplify R2 r with [x := y]"));
  }

  @Test
  public void testFindHeadSimplification() {
    PartialProof pp = setupProof("sum1(suc(x)) = sum2(y) | x + 1 = y");
    Settings.smtSolver = null;
    DeductionStep step = AutoSimplifier.createSingleStep(pp);
    assertTrue(step.commandDescription().equals("simplify R8 l1.*1 with []"));
  }

  @Test
  public void testSimplifyFully() {
    PartialProof pp = setupProof("sum1(iter(x, i, z)) = 1 + len(cons(i, y)) | x > i + 1");
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(false, true, false, true);
    solver.setDefaultAnswer(false);
    Settings.smtSolver = solver;
    List<DeductionStep> steps = AutoSimplifier.simplifyFully(pp);
    assertTrue(steps.size() == 7);
    assertTrue(solver.queryNumberQuestions() == 6);
    // x > i + 1 => i > x
    assertTrue(solver.queryQuestion(0).equals("(1 + i2 >= i1) or (i2 >= 1 + i1)\n"));
    // x > i + 1 => x >= i
    assertTrue(solver.queryQuestion(1).equals("(1 + i2 >= i1) or (i1 >= i2)\n"));
    // x > i + 1 /\ i1 = i + 1 /\ z1 = z + i => i1 > x
    assertTrue(solver.queryQuestion(2).equals(
      "(1 + i2 >= i1) or (i3 # 1 + i2) or (i4 # i5 + i2) or (i3 >= 1 + i1)\n"));
  }
}

