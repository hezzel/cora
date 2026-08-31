/**************************************************************************************************
 Copyright 2025 Cynthia Kop & Liye Guo

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.template;

import charlie.reader.CoraInputReader;
import static charlie.trs.TrsFactory.LCSTRS;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class TailupMatcherTest {
  @Test
  public void testFactorial() {
    var trs = CoraInputReader.readTrsFromString(
      "fact :: Int -> Int -> Int -> Int\n" +
        "fact(n, i, a) -> a | i > n\n" +
        "fact(n, i, a) -> fact(n, i + 1, i * a) | i <= n\n",
      LCSTRS);
    TailupMatcher matcher = TailupMatcher.match(trs.queryRules());
    assertNotNull(matcher);
    var equRul = matcher.generateEquationAndRule();
    assertEquals(
      "fact(n, i, a) ≈ _tailup([*], i, _x, _y, a) | _x ≤ i ∧ i ≤ _y ∧ _y = n",
      equRul.fst().toString());
    assertNull(equRul.snd());
  }

  @Test
  public void testFactorial0() {
    var trs = CoraInputReader.readTrsFromString(
      "fact0 :: Int -> Int -> Int\n" +
        "fact0(i, a) -> a | i > 0\n" +
        "fact0(i, a) -> fact0(i + 1, i * a) | i <= 0\n",
      LCSTRS);
    TailupMatcher matcher = TailupMatcher.match(trs.queryRules());
    assertNotNull(matcher);
    var equRul = matcher.generateEquationAndRule();
    assertEquals(
      "fact0(i, a) ≈ _tailup([*], i, _x, _y, a) | _x ≤ i ∧ i ≤ _y ∧ _y = 0",
      equRul.fst().toString());
    assertNull(equRul.snd());
  }

  @Test
  public void testFactorial10() {
    var trs = CoraInputReader.readTrsFromString(
      "fact10 :: Int -> Int -> Int\n" +
        "fact10(i, a) -> a | i > 10\n" +
        "fact10(i, a) -> fact10(i + 1, i * a) | i <= 10\n",
      LCSTRS);
    TailupMatcher matcher = TailupMatcher.match(trs.queryRules());
    assertNotNull(matcher);
    var equRul = matcher.generateEquationAndRule();
    assertEquals(
      "fact10(i, a) ≈ _tailup([*], i, _x, _y, a) | _x ≤ i ∧ i ≤ _y ∧ _y = 10",
      equRul.fst().toString());
    assertNull(equRul.snd());
  }

  @Test
  public void testSum() {
    var trs = CoraInputReader.readTrsFromString(
      "sum :: Int -> Int -> Int -> Int\n" +
        "sum(n, i, a) -> a | n < 1 + i\n" +
        "sum(n, i, a) -> sum(n, 1 + i, a + i) | n >= 1 + i\n",
      LCSTRS);
    TailupMatcher matcher = TailupMatcher.match(trs.queryRules());
    assertNotNull(matcher);
    var equRul = matcher.generateEquationAndRule();
    assertEquals(
      "sum(n, i, a) ≈ _tailup(_f, i, _x, _y, a) | _x ≤ i ∧ i ≤ _y ∧ _y = n - 1",
      equRul.fst().toString());
    assertEquals(
      "_f(i, a) → a + i",
      equRul.snd().toString());
  }

  @Test
  public void testTooFewRules() {
    var trs = CoraInputReader.readTrsFromString(
      "sum :: Int -> Int -> Int -> Int\n" +
        "sum(n, i, a) -> a | n < 1 + i\n",
      LCSTRS);
    TailupMatcher matcher = TailupMatcher.match(trs.queryRules());
    assertNull(matcher);
  }

  @Test
  public void testTooManyRules() {
    var trs = CoraInputReader.readTrsFromString(
      "sum :: Int -> Int -> Int -> Int\n" +
        "sum(n, i, a) -> a | n < 10\n" +
        "sum(n, i, a) -> a | n < 1 + i\n" +
        "sum(n, i, a) -> sum(n, 1 + i, a + i) | n >= 1 + i\n",
      LCSTRS);
    TailupMatcher matcher = TailupMatcher.match(trs.queryRules());
    assertNull(matcher);
  }

  @Test
  public void testAccumulatorNotOnLeftHandSide() {
    var trs = CoraInputReader.readTrsFromString(
      "sum :: Int -> Int -> Int -> Int\n" +
        "sum(n, i, a) -> b | n < 1 + i\n" +
        "sum(n, i, a) -> sum(n, 1 + i, a + i) | n >= 1 + i\n",
      LCSTRS);
    TailupMatcher matcher = TailupMatcher.match(trs.queryRules());
    assertNull(matcher);
  }
}
