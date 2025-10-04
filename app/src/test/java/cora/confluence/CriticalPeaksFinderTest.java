/**************************************************************************************************
 Copyright 2025 Cynthia Kop and Liye Guo

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.confluence;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import java.util.Arrays;

import charlie.reader.CoraInputReader;
import charlie.smt.Valuation;
import charlie.smt.SmtProblem;
import charlie.smt.SmtSolver;
import charlie.trs.TRS;
import static charlie.trs.TrsFactory.LCSTRS;
import cora.config.Settings;

class CriticalPeaksFinderTest {
  private static class DummySat implements SmtSolver {
    public Answer checkSatisfiability(SmtProblem problem) {
      return new Answer.YES(new Valuation());
    }

    public boolean checkValidity(SmtProblem problem) {
      fail();
      return false;
    }
  }

  private static void testWithDummySat(TRS trs, String[] exp) {
    Settings.smtSolver = new DummySat();
    var cps = CriticalPeaksFinder.criticalPeaks(trs, false);
    assertEquals(exp.length, cps.size());
    assertTrue(cps.stream().map(CriticalPeak::toString).toList().containsAll(Arrays.asList(exp)));
  }

  @Test
  public void testStringRewriting() {
    var trs = CoraInputReader.readTrsFromString(
      "b :: o -> o\n" +
      "w :: o -> o\n" +
      "b(w(x)) -> w(w(w(b(x))))\n" +
      "w(b(x)) -> b(x)\n" +
      "b(b(x)) -> w(w(w(w(x))))\n" +
      "w(w(x)) -> w(x)\n",
      LCSTRS);
    var exp = new String[] {
      "⟨b(w(b(x))), b(b(x)) ≈ w(w(w(b(b(x)))))⟩",
      "⟨b(w(w(x))), b(w(x)) ≈ w(w(w(b(w(x)))))⟩",
      "⟨w(b(w(x))), w(w(w(w(b(x))))) ≈ b(w(x))⟩",
      "⟨w(b(b(x))), w(w(w(w(w(x))))) ≈ b(b(x))⟩",
      "⟨b(b(w(x))), b(w(w(w(b(x))))) ≈ w(w(w(w(w(x)))))⟩",
      "⟨b(b(b(x))), b(w(w(w(w(x))))) ≈ w(w(w(w(b(x)))))⟩",
      "⟨w(w(b(x))), w(b(x)) ≈ w(b(x))⟩",
      "⟨w(w(w(x))), w(w(x)) ≈ w(w(x))⟩" };
    testWithDummySat(trs, exp);
  }

  @Test
  public void testPartialApplication() {
    var trs = CoraInputReader.readTrsFromString(
      "f :: a -> b\n" +
      "g :: a -> b\n" +
      "h :: a -> c\n" +
      "u :: b -> c\n" +
      "f -> g\n" +
      "u(f(x)) -> h(x)\n",
      LCSTRS);
    var exp = new String[] {
      "⟨u(f(x)), u(g(x)) ≈ h(x)⟩" };
    testWithDummySat(trs, exp);
  }

  @Test
  public void testCalculation() {
    var trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int\n" +
      "f(x + y) -> f(x) + f(y)\n",
      LCSTRS);
    var exp = new String[] {
      "⟨f(x + y), f(_z) ≈ f(x) + f(y) | _z = x + y⟩" };
    testWithDummySat(trs, exp);
  }

  @Test
  public void testSameRuleAtRoot() {
    var trs = CoraInputReader.readTrsFromString(
      "readint :: Int\n" +
      "readint -> x",
      LCSTRS);
    var exp = new String[] {
      "⟨readint, x__1 ≈ x__2 | x__1 = x__1 ∧ x__2 = x__2⟩" };
    testWithDummySat(trs, exp);
  }

  @Test
  public void testSymmetry() {
    var trs = CoraInputReader.readTrsFromString(
      "f :: (Int -> Int) -> Int -> Int -> Int -> Int\n" +
      "f(G, n, m, x) -> f(G, n - 1, m, G(x)) | n > 0\n" +
      "f(G, n, m, x) -> f(G, m - 1, n, G(x)) | m > 0\n",
      LCSTRS);
    var exp = new String[] {
      "⟨f(G, n, m, x), f(G, m - 1, n, G(x)) ≈ f(G, n - 1, m, G(x)) | m > 0 ∧ n > 0⟩" };
    testWithDummySat(trs, exp);
  }

  @Test
  public void testAsymmetry() {
    var trs = CoraInputReader.readTrsFromString(
      "f :: (o -> o) -> o -> o\n" +
      "f(x) -> x\n" +
      "f(x, y) -> y\n",
      LCSTRS);
    var exp = new String[] {
      "⟨f(x, y), x(y) ≈ y⟩" };
    testWithDummySat(trs, exp);
  }
}
