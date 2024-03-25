/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.termination;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import cora.terms.FunctionSymbol;
import cora.terms.TheoryFactory;
import cora.trs.TRS;
import cora.reader.CoraInputReader;

public class HorpoTest {
  private TRS makeTrs(String txt) {
    return CoraInputReader.readTrsFromString(txt);
  }

/**
 * Outcommented because they are all pretty heavy tests, several of which actually invoke the
 * external SMT solver.  Uncomment when you are actually fiddling with the Horpo module!

  @Test
  public void testComputeIntegerVariableBound() {
    TRS trs;
    trs = makeTrs("f :: Int -> Int\n" +
                  "g :: Int -> Int -> Int\n" +
                  "g(x, y) -> g(x - 1, y) | x > 0\n" +
                  "f(x) → g(4211, -3000) | x > 12\n" +
                  "f(4000) → f(16)");
    Horpo horpo = new Horpo(trs);
    assertTrue(horpo.queryIntegerVariableBound() == 8422);
    trs = makeTrs("f :: Int -> Int\n" +
                  "g :: Int -> Int -> Int\n" +
                  "g(x, y) -> g(x - 1, y) | x < -5000\n" +
                  "f(x) → g(4211, -3000) | x > 12\n" +
                  "f(4000) → f(16)");
    horpo = new Horpo(trs);
    assertTrue(horpo.queryIntegerVariableBound() == 10000);
    trs = makeTrs("f :: Int -> Int\n" +
                  "g :: Int -> Int -> Int\n" +
                  "g(x, y) -> g(x - 1, y) | x < -5000\n" +
                  "f(x) → g(4211, -3000) | x > 12\n" +
                  "f(9001) → f(16)");
    horpo = new Horpo(trs);
    assertTrue(horpo.queryIntegerVariableBound() == 18002);
    trs = makeTrs("f :: Int -> Int\n" +
                  "g :: Int -> Int -> Int\n" +
                  "g(x, y) -> g(x - 1, y) | x < -500\n" +
                  "f(x) → g(421, -300) | x > 12\n" +
                  "f(401) → f(16)");
    horpo = new Horpo(trs);
    assertTrue(horpo.queryIntegerVariableBound() == 1000);
  }

  @Test
  public void testPrecedenceFor() {
    TRS trs;
    trs = makeTrs("f :: Int -> Int\n" +
                  "g :: Int -> Int -> Int\n" +
                  "g(x, y) -> g(x - 1, y) | x > 0\n" +
                  "f(x) → g(4211, -3000) | x > 12\n" +
                  "f(4000) → f(16)");
    Horpo horpo = new Horpo(trs);
    FunctionSymbol f = trs.queryAlphabet().lookup("f");
    FunctionSymbol g = trs.queryAlphabet().lookup("g");
    FunctionSymbol minus = TheoryFactory.minusSymbol;
    assertTrue(horpo.getPrecedenceFor(f).queryIndex() == 1);
    assertTrue(horpo.getPrecedenceFor(minus).queryIndex() == 2);
    assertTrue(horpo.getPrecedenceFor(f).queryIndex() == 1);
    assertTrue(horpo.getPrecedenceFor(g).queryIndex() == 3);
    assertTrue(horpo.getPrecedenceFor(minus).queryIndex() == 2);
    System.out.println(horpo.toString());
    assertTrue(horpo.toString().equals(
      "b2\n" +
      "b3\n" +
      "b4\n" +
      "(>= i1 0)\n" +
      "(> 0 i2)\n" +
      "(>= i3 0)\n" +
      "  b2 => 0: g(x, y) ≻{x > 0} g(x - 1, y)\n" +
      "  b3 => 1: f(x) ≻{x > 12} g(4211, -3000)\n" +
      "  b4 => 2: f(4000) ≻{true} f(16)\n"));
  }

  @Test
  public void testStatusFor() {
    TRS trs;
    trs = makeTrs("f :: Int -> Int\n" +
                  "g :: Int -> Int -> Int\n" +
                  "g(x, y) -> g(x - 1, y) | x > 0\n" +
                  "f(x) → g(4211, -3000) | x > 12\n" +
                  "f(4000) → f(16)");
    Horpo horpo = new Horpo(trs);
    FunctionSymbol f = trs.queryAlphabet().lookup("f");
    FunctionSymbol g = trs.queryAlphabet().lookup("g");
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    assertTrue(horpo.getStatusFor(f) == null);
    assertTrue(horpo.getStatusFor(plus).queryIndex() == 1);
    assertTrue(horpo.getStatusFor(f) == null);
    assertTrue(horpo.getPrecedenceFor(f).queryIndex() == 2);
    assertTrue(horpo.getStatusFor(g).queryIndex() == 3);
    assertTrue(horpo.getStatusFor(plus).queryIndex() == 1);
    assertTrue(horpo.toString().equals(
      "b2\n" +
      "b3\n" +
      "b4\n" +
      "(>= i1 1)\n" +
      "(>= 2 i1)\n" +
      "(>= i2 0)\n" +
      "(>= i3 1)\n" +
      "(>= 2 i3)\n" +
      "  b2 => 0: g(x, y) ≻{x > 0} g(x - 1, y)\n" +
      "  b3 => 1: f(x) ≻{x > 12} g(4211, -3000)\n" +
      "  b4 => 2: f(4000) ≻{true} f(16)\n"));
  }

  @Test
  public void testSimplifyTwoDistinctConstants() {
    // test splitting > into parts, and 1b, 2b, 3c
    TRS trs = makeTrs("a :: o b :: o a → b");
    Horpo horpo = new Horpo(trs);
    assertTrue(horpo.toString().equals(
      "b2\n" +
      "  b2 => 0: a ≻{true} b\n"));
    assertTrue(horpo.handleTodo());
    assertTrue(horpo.toString().equals(
      "b2\n" +
      "(or (not b2) b3 b4 b5 b6)\n" +
      "  b3 => 0: a ≻{true} b by 2a\n" +
      "  b4 => 0: a ≻{true} b by 2c\n" +
      "  b5 => 0: a ≻{true} b by 2d\n" +
      "  b6 => 0: a ≻{true} b by 2b\n"));
    assertTrue(horpo.handleTodo());
    assertTrue(horpo.handleTodo());
    assertTrue(horpo.handleTodo());
    assertTrue(horpo.handleTodo());
    assertTrue(horpo.toString().equals(
      "b2\n" +
      "(or (not b2) b3 b4 b5 b6)\n" +
      "(not b3)\n" +
      "(not b4)\n" +
      "(not b5)\n" +
      "(or (not b6) b7)\n" +
      "  b7 => 0: a ▷{true} b\n"));
    assertTrue(horpo.handleTodo());
    assertTrue(horpo.toString(-2, 0).equals(
      "(or (not b6) b7)\n" +
      "(or (not b7) b8 b9 b10 b11 b12 b13)\n" +
      "  b8 => 0: a ▷{true} b by 3f\n" +
      "  b9 => 0: a ▷{true} b by 3a\n" +
      "  b10 => 0: a ▷{true} b by 3c\n" +
      "  b11 => 0: a ▷{true} b by 3d\n" +
      "  b12 => 0: a ▷{true} b by 3e\n" +
      "  b13 => 0: a ▷{true} b by 3b\n"));
    assertTrue(horpo.handleTodo());
    assertTrue(horpo.handleTodo());
    assertTrue(horpo.handleTodo());
    assertTrue(horpo.toString(-4, 0).equals(
      "(not b9)\n" +
      "(>= i1 0)\n" +
      "(>= i2 0)\n" +
      "(or (not b10) (> i1 i2))\n" +
      "  b11 => 0: a ▷{true} b by 3d\n" +
      "  b12 => 0: a ▷{true} b by 3e\n" +
      "  b13 => 0: a ▷{true} b by 3b\n"));
    assertTrue(horpo.handleTodo());
    assertTrue(horpo.handleTodo());
    assertTrue(horpo.handleTodo());
    assertFalse(horpo.handleTodo());
  }

  // NOTE: this test is currently broken: all b{i} should be replaced by b{i+1}
  @Test
  public void testSimplifyReductionToFreshVariable() {
    // additionally test splitting ≥ into parts, and 3a, 3f
    TRS trs = makeTrs("f :: (o → o) → o → o → Int a :: o → o b :: o f(a, b, y) → x");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 5; i++) assertTrue(horpo.handleTodo());
    assertTrue(horpo.toString(-1, 0).equals(
      "(or (not b5) b6)\n" +
      "  b6 => 0: f(a, b, y) ▷{true ∧ x = x} x\n"));
    assertTrue(horpo.handleTodo());
    assertTrue(horpo.toString(-1, 0).equals(
      "(or (not b6) b7 b8 b9 b10 b11 b12)\n" +
      "  b7 => 0: f(a, b, y) ▷{true ∧ x = x} x by 3f\n" +
      "  b8 => 0: f(a, b, y) ▷{true ∧ x = x} x by 3a\n" +
      "  b9 => 0: f(a, b, y) ▷{true ∧ x = x} x by 3c\n" +
      "  b10 => 0: f(a, b, y) ▷{true ∧ x = x} x by 3d\n" +
      "  b11 => 0: f(a, b, y) ▷{true ∧ x = x} x by 3e\n" +
      "  b12 => 0: f(a, b, y) ▷{true ∧ x = x} x by 3b\n"));
    assertTrue(horpo.handleTodo());
    assertTrue(horpo.toString(-1, 0).equals(
      "(or (not b6) b7 b8 b9 b10 b11 b12)\n" +
      "  b8 => 0: f(a, b, y) ▷{true ∧ x = x} x by 3a\n" +
      "  b9 => 0: f(a, b, y) ▷{true ∧ x = x} x by 3c\n" +
      "  b10 => 0: f(a, b, y) ▷{true ∧ x = x} x by 3d\n" +
      "  b11 => 0: f(a, b, y) ▷{true ∧ x = x} x by 3e\n" +
      "  b12 => 0: f(a, b, y) ▷{true ∧ x = x} x by 3b\n"));
    assertTrue(horpo.handleTodo());
    assertTrue(horpo.toString(-2, 0).equals(
      "(or (not b6) b7 b8 b9 b10 b11 b12)\n" +
      "(or (not b8) b13 b14)\n" +
      "  b9 => 0: f(a, b, y) ▷{true ∧ x = x} x by 3c\n" +
      "  b10 => 0: f(a, b, y) ▷{true ∧ x = x} x by 3d\n" +
      "  b11 => 0: f(a, b, y) ▷{true ∧ x = x} x by 3e\n" +
      "  b12 => 0: f(a, b, y) ▷{true ∧ x = x} x by 3b\n" +
      "  b13 => 0: b ≽{true ∧ x = x} x\n" +
      "  b14 => 0: y ≽{true ∧ x = x} x\n"));
    for (int i = 0; i < 5; i++) assertTrue(horpo.handleTodo());
    assertTrue(horpo.toString(-6, 0).equals(
      "(or (not b8) b13 b14)\n" +
      "(not b9)\n" +
      "(not b10)\n" +
      "(not b11)\n" +
      "(not b12)\n" +
      "(or (not b13) b15 b16 b17 b18)\n" +
      "  b14 => 0: y ≽{true ∧ x = x} x\n" +
      "  b15 => 0: b ≽{true ∧ x = x} x by 1c\n" +
      "  b16 => 0: b ≽{true ∧ x = x} x by 1a\n" +
      "  b17 => 0: b ≽{true ∧ x = x} x by 1b\n" +
      "  b18 => 0: b ≽{true ∧ x = x} x by 1d\n"));
    for (int i = 0; i < 6; i++) assertTrue(horpo.handleTodo());
    assertTrue(horpo.toString(-1, 0).equals(
      "(not b19)\n" +
      "  b20 => 0: y ≽{true ∧ x = x} x by 1a\n" +
      "  b21 => 0: y ≽{true ∧ x = x} x by 1b\n" +
      "  b22 => 0: y ≽{true ∧ x = x} x by 1d\n" +
      "  b23 => 0: b ≻{true ∧ x = x} x\n"));
    assertTrue(horpo.handleTodo());
    assertTrue(horpo.toString(-2, 0).equals(
      "(not b19)\n" +
      "(not b20)\n" +
      "  b21 => 0: y ≽{true ∧ x = x} x by 1b\n" +
      "  b22 => 0: y ≽{true ∧ x = x} x by 1d\n" +
      "  b23 => 0: b ≻{true ∧ x = x} x\n"));
    for (int i = 0; i < 19; i++) assertTrue(horpo.handleTodo());
    assertFalse(horpo.handleTodo());
  }

  // NOTE: this test is currently broken: all b{i} should be replaced by b{i+1}
  @Test
  public void testIntegerComparison() {
    // test other cases of 3a and 3c, and 3b
    TRS trs = makeTrs("f :: Int → Int f(x) → x - 1 | x > 3");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 5; i++) horpo.handleTodo();
    assertTrue(horpo.toString().equals(
      "b1\n" +
      "(or (not b1) b2 b3 b4 b5)\n" +
      "(not b2)\n" +
      "(not b3)\n" +
      "(not b4)\n" +
      "(or (not b5) b6)\n" +
      "  b6 => 0: f(x) ▷{x > 3} x - 1\n"));
    for (int i = 0; i < 3; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-4, 0).equals(
      "(or (not b5) b6)\n" +
      "(or (not b6) b7 b8 b9 b10 b11 b12)\n" +
      "(not b7)\n" +
      "(or (not b8) b13)\n" +
      "  b9 => 0: f(x) ▷{x > 3} x - 1 by 3c\n" +
      "  b10 => 0: f(x) ▷{x > 3} x - 1 by 3d\n" +
      "  b11 => 0: f(x) ▷{x > 3} x - 1 by 3e\n" +
      "  b12 => 0: f(x) ▷{x > 3} x - 1 by 3b\n" +
      "  b13 => 0: x ≽{x > 3} x - 1\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-6, 0).equals(
      "(or (not b8) b13)\n" +
      "(>= i1 0)\n" +
      "(> 0 i2)\n" +
      "(or (not b9) (> i1 i2))\n" +
      "(or (not b9) b14)\n" +
      "(or (not b9) b15)\n" +
      "  b10 => 0: f(x) ▷{x > 3} x - 1 by 3d\n" +
      "  b11 => 0: f(x) ▷{x > 3} x - 1 by 3e\n" +
      "  b12 => 0: f(x) ▷{x > 3} x - 1 by 3b\n" +
      "  b13 => 0: x ≽{x > 3} x - 1\n" +
      "  b14 => 0: f(x) ▷{x > 3} x\n" +
      "  b15 => 0: f(x) ▷{x > 3} -1\n"));
    for (int i = 0; i < 3; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-5, 0).equals(
      "(or (not b9) b15)\n" +
      "(not b10)\n" +
      "(not b11)\n" +
      "(or (not b12) b16)\n" +
      "(or (not b12) b15)\n" +
      "  b13 => 0: x ≽{x > 3} x - 1\n" +
      "  b14 => 0: f(x) ▷{x > 3} x\n" +
      "  b15 => 0: f(x) ▷{x > 3} -1\n" +
      "  b16 => 0: f(x) ▷{x > 3} +(x)\n"));
    for (int i = 0; i < 5; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b17)\n" +
      "  b18 => 0: x ≽{x > 3} x - 1 by 1a\n"));
    assertTrue(horpo.handleTodo());
    assertTrue(horpo.toString(-2,1).equals(
      "(not b17)\n" +
      "(or (not b18) b0)\n" +
      "  b19 => 0: x ≽{x > 3} x - 1 by 1b\n"));
    for (int i = 0; i < 3; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b20)\n" +
      "  b22 => 0: f(x) ▷{x > 3} x by 3a\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-2,-1).equals(
      "(not b20)\n" +
      "(or (not b22) b39)\n" +
      "  b39 => 0: x ≽{x > 3} x\n"));
    for (int i = 0; i < 4; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b26)\n" +
      "  b27 => 0: f(x) ▷{x > 3} -1 by 3f\n"));
    assertTrue(horpo.toString(-1,-1).equals(
      "(not b26)\n" +
      "  b39 => 0: x ≽{x > 3} x\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-1,-1).equals(
      "(not b26)\n" +
      "  b39 => 0: x ≽{x > 3} x\n"));
    for (int i = 0; i < 6; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b33)\n" +
      "  b34 => 0: f(x) ▷{x > 3} +(x) by 3a\n"));
    horpo.handleTodo();
    // different types in select
    assertTrue(horpo.toString(-1,1).equals(
      "(not b34)\n" +
      "  b35 => 0: f(x) ▷{x > 3} +(x) by 3c\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-3,1).equals(
      "(not b34)\n" +
      "(or (not b35) (> i1 i2))\n" +
      "(or (not b35) b14)\n" +
      "  b36 => 0: f(x) ▷{x > 3} +(x) by 3d\n"));
    for (int i = 0; i < 6; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,3).equals(
      "(or (not b41) b50 b51 b52 b53 b54 b55)\n" +
      "  b42 => 0: x ≽{x > 3} x by 1c\n" +
      "  b43 => 0: x ≽{x > 3} x by 1a\n" +
      "  b44 => 0: x ≽{x > 3} x by 1b\n"));
    for (int i = 0; i < 3; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-2,1).equals(
      "(or (not b41) b50 b51 b52 b53 b54 b55)\n" +
      "(not b44)\n" +
      "  b45 => 0: x ≽{x > 3} x by 1d\n"));
    for (int i = 0; i < 2; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,2).equals(
      "(not b46)\n" +
      "  b47 => 0: x ≽{x > 3} -1 by 1a\n" +
      "  b48 => 0: x ≽{x > 3} -1 by 1b\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-2,1).equals(
      "(not b46)\n" +
      "(or (not b47) b0)\n" +
      "  b48 => 0: x ≽{x > 3} -1 by 1b\n"));
    for (int i = 0; i < 8; i++) assertTrue(horpo.handleTodo());
    assertFalse(horpo.handleTodo());
  }

  // NOTE: this test is currently broken: all b{i} should be replaced by b{i+1}
  @Test
  public void testIntegerComparisonUp() {
    TRS trs = makeTrs("f :: Int → Int f(x) → x + y | x < 100 ∧ y > 0");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 17; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b17)\n" +
      "  b18 => 0: x ≽{x < 100 ∧ y > 0} x + y by 1a\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-2,1).equals(
      "(not b17)\n" +
      "(or (not b18) (not b0))\n" +
      "  b19 => 0: x ≽{x < 100 ∧ y > 0} x + y by 1b\n"));
  }

  // NOTE: this test is currently broken: all b{i} should be replaced by b{i+1}
  @Test
  public void testBooleanGeqStrict() {
    TRS trs = makeTrs("f :: Bool → Bool f(x) → x ∧ false | x");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 17; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b17)\n" +
      "  b18 => 0: x ≽{x} x ∧ false by 1a\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b17)\n" +
      "  b19 => 0: x ≽{x} x ∧ false by 1b\n"));
  }

  // NOTE: this test is currently broken: all b{i} should be replaced by b{i+1}
  @Test
  public void testBooleanGeqNonStrict() {
    TRS trs = makeTrs("f :: Bool → Bool f(x) → x ∧ true | x");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 17; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b17)\n" +
      "  b18 => 0: x ≽{x} x ∧ true by 1a\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b17)\n" +
      "  b19 => 0: x ≽{x} x ∧ true by 1b\n"));
  }

  // NOTE: this test is currently broken: all b{i} should be replaced by b{i+1}
  @Test
  public void testBooleanGeqFails() {
    TRS trs = makeTrs("f :: Bool → Bool f(x) → x ∨ true | ¬x");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 17; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b17)\n" +
      "  b18 => 0: x ≽{¬x} x ∨ true by 1a\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-2,1).equals(
      "(not b17)\n" +
      "(not b18)\n" +
      "  b19 => 0: x ≽{¬x} x ∨ true by 1b\n"));
  }

  // NOTE: this test is currently broken: all b{i} should be replaced by b{i+1}
  @Test
  public void testTheoryComparisonWrongTheoryTypes() {
    TRS trs = makeTrs("f :: Int → Bool f(y) → false");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 14; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b14)\n" +
      "  b15 => 0: y ≽{true} false by 1a\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-2,1).equals(
      "(not b14)\n" +
      "(not b15)\n" +
      "  b16 => 0: y ≽{true} false by 1b\n"));
  }

  // NOTE: this test is currently broken: all b{i} should be replaced by b{i+1}
  @Test
  public void testLeftNotBounded() {
    TRS trs = makeTrs("f :: Int → Int f(x) → x - 1 | x != 0");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 17; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b17)\n" +
      "  b18 => 0: x ≽{x ≠ 0} x - 1 by 1a\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-3,1).equals(
      "(not b17)\n" +
      "(or (not b18) (not b0))\n" +
      "(or (not b18) b0)\n" +
      "  b19 => 0: x ≽{x ≠ 0} x - 1 by 1b\n"));
  }

  // NOTE: this test is currently broken: all b{i} should be replaced by b{i+1}
  @Test
  public void testDecreaseInTheoryIntegerArgument() {
    TRS trs = makeTrs("f :: Int → Int f(x) → f(x - 1) | x > 12");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 2; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b2)\n" +
      "  b3 => 0: f(x) ≻{x > 12} f(x - 1) by 2c\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-3,-3).equals(
      "(not b2)\n" +
      "(or (not b3) b6)\n" +
      "(or (not b3) b7)\n" +
      "  b5 => 0: f(x) ≻{x > 12} f(x - 1) by 2b\n" +
      "  b6 => 0: x ≽{x > 12} x - 1\n" +
      "  b7 => 0: x ≻{x > 12} x - 1\n"));
    for (int i = 0; i < 9; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b12)\n" +
      "  b13 => 0: x ≻{x > 12} x - 1 by 2a\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-2,-1).equals(
      "(not b12)\n" +
      "(or (not b13) b0)\n" +
      "  b22 => 0: f(x) ▷{x > 12} f(x - 1) by 3b\n"));
  }

  // NOTE: this test is currently broken: all b{i} should be replaced by b{i+1}
  @Test
  public void testDecreaseInTheoryBooleanArgument() {
    TRS trs = makeTrs("f :: Bool → unit f(x) → f(¬x) | x");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 12; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b12)\n" +
      "  b13 => 0: x ≻{x} ¬x by 2a\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b12)\n" +
      "  b14 => 0: x ≻{x} ¬x by 2c\n"));
  }

  // NOTE: this test is currently broken: all b{i} should be replaced by b{i+1}
  @Test
  public void testFailedDecreaseInTheoryArgument() {
    TRS trs = makeTrs("f :: Int → Int f(x) → f(x + y) | x < 10 ∧ y ≥ 0");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 12; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-2,1).equals(
      "(not b11)\n" +
      "(not b12)\n" +
      "  b13 => 0: x ≻{x < 10 ∧ y ≥ 0} x + y by 2a\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-3,1).equals(
      "(not b12)\n" +
      "(or (not b13) (not b0))\n" +
      "(or (not b13) b0)\n" +
      "  b14 => 0: x ≻{x < 10 ∧ y ≥ 0} x + y by 2c\n"));
  }

  // NOTE: this test is currently broken: all b{i} should be replaced by b{i+1}
  @Test
  public void testFailedDecreaseInTheoryBooleanArgument() {
    TRS trs = makeTrs("f :: Bool → unit f(x) → f(false) | x ∨ ¬x");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 12; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b12)\n" +
      "  b13 => 0: x ≻{x ∨ ¬x} false by 2a\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-2,1).equals(
      "(not b12)\n" +
      "(not b13)\n" +
      "  b14 => 0: x ≻{x ∨ ¬x} false by 2c\n"));
  }

  // NOTE: this test is currently broken: all b{i} should be replaced by b{i+1}
  @Test
  public void testVartermDecrease() {
    TRS trs = makeTrs("f :: o → o a :: o b :: o c :: o {x :: o → o → o} f(x(a,b)) -> f(x(a, c))");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 11; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(or (not b11) b7)\n" +
      "  b12 => 0: x(a, b) ≽{true} x(a, c) by 1d\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-3,-2).equals(
      "(or (not b11) b7)\n" +
      "(or (not b12) b23)\n" +
      "(or (not b12) b24)\n" +
      "  b23 => 0: x(a) ≽{true} x(a)\n" +
      "  b24 => 0: b ≽{true} c\n"));
    for (int i = 0; i < 2; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b14)\n" +
      "  b15 => 0: x(a, b) ≻{true} x(a, c) by 2d\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-4,-4).equals(
      "(not b14)\n" +
      "(or (not b15) b25)\n" +
      "(or (not b15) b24)\n" +
      "(or (not b15) b26 b27)\n" +
      "  b24 => 0: b ≽{true} c\n" +
      "  b25 => 0: a ≽{true} a\n" +
      "  b26 => 0: a ≻{true} a\n" +
      "  b27 => 0: b ≻{true} c\n"));
  }

  // NOTE: this test is currently broken: all b{i} should be replaced by b{i+1}
  @Test
  public void testAppWhenArgumentTypesDiffer() {
    TRS trs = makeTrs("f :: o → o g :: (o → o) → o h :: a → o a :: o b :: o → o " +
      "f(f(a)) → g(b) f(h(x)) → f(a)");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 44; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(or (not b44) b80)\n" +
      "  b45 => 0: f(a) ≽{true} g(b) by 1d\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b45)\n" +
      "  b46 => 0: f(f(a)) ▷{true} b by 3f\n"));
    for (int i = 0; i < 21; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(or (not b66) b82)\n" +
      "  b67 => 1: h(x) ≽{true} f(a) by 1d\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-2,-3).equals(
      "(or (not b67) b83)\n" +
      "(or (not b67) b81)\n" +
      "  b81 => 1: x ≽{true} a\n" +
      "  b82 => 1: h(x) ≻{true} f(a)\n" +
      "  b83 => 1: h ≽{true} f\n"));
  }

  // NOTE: this test is currently broken: all b{i} should be replaced by b{i+1}
  @Test
  public void testLexWithDifferentArgumentCounts() {
    TRS trs = makeTrs("f :: o → o → o g :: o → o → o a :: o b :: o f(a) -> g(f(b,b))");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 17; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b17)\n" +
      "  b18 => 0: f(a) ▷{true} f(b, b) by 3d\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-6,-2).equals(
      "(not b17)\n" +
      "(>= i3 1)\n" +
      "(>= 2 i3)\n" +
      "(or (not b18) (= i3 1))\n" +
      "(or (not b18) b28)\n" +
      "(or (not b18) b29)\n" +
      "  b28 => 0: a ≻{true} b\n" +
      "  b29 => 0: f(a) ▷{true} b\n"));
  }

  // NOTE: this test is currently broken: all b{i} should be replaced by b{i+1}
  @Test
  public void testFullLex() {
    TRS trs = makeTrs("f :: o → o → o → o a :: o b :: o c :: o f(a,b,c) → f(b,c,a)");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 5; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,6).equals(
      "(or (not b5) b12)\n" +
      "  b6 => 0: a ≽{true} b\n" +
      "  b7 => 0: a ≻{true} b\n" +
      "  b8 => 0: b ≽{true} c\n" +
      "  b9 => 0: b ≻{true} c\n" +
      "  b10 => 0: c ≽{true} a\n" +
      "  b11 => 0: c ≻{true} a\n"));
    for (int i = 0; i < 34; i++) horpo.handleTodo();
    assertTrue(horpo.toString(-1,1).equals(
      "(not b39)\n" +
      "  b40 => 0: f(a, b, c) ▷{true} f(b, c, a) by 3d\n"));
    horpo.handleTodo();
    assertTrue(horpo.toString(-13,-2).equals(
      "(not b39)\n" +
      "(>= i1 1)\n" +
      "(>= 3 i1)\n" +
      "(or (not b40) (= i1 1))\n" +
      "(>= i2 1)\n" +
      "(>= 3 i2)\n" +
      "(or (not b40) (not (> i2 1)) b6)\n" +
      "(or (not b40) (not (> i2 2)) b8)\n" +
      "(or (not b40) (not (= i2 1)) b7)\n" +
      "(or (not b40) (not (= i2 2)) b9)\n" +
      "(or (not b40) (not (= i2 3)) b11)\n" +
      "(or (not b40) b49)\n" +
      "(or (not b40) b50)\n" +
      "  b49 => 0: f(a, b, c) ▷{true} c\n" +
      "  b50 => 0: f(a, b, c) ▷{true} a\n"));
  }

  // @Test
  public void testFullMul() {
    // the Mul case gives such huge requirements that we just print it for inspection rather than
    // saving what is supposed to come out
    TRS trs = makeTrs("f :: o → a → (o → o) → o → b → o\n" +
                      "v1 :: o v2 :: a v3 :: o → o v4 :: o v5 :: b\n" +
                      "f(x,y,z,u,w) -> f(v1,v2,v3,v4,v5)");
    Horpo horpo = new Horpo(trs);
    for (int i = 0; i < 60; i++) horpo.handleTodo();
    System.out.println(horpo.toString(-1,1));
    horpo.handleTodo();
    System.out.println(horpo.toString(-90,-28));
  }

  @Test
  public void testMulSuccessWithTWo() {
    TRS trs = makeTrs("f :: Int -> Int -> unit\n" +
                      "f(x, y) -> f(y-1, x) | x > 0 ∧ y > 0\n");
    Horpo horpo = new Horpo(trs);
    Horpo.HorpoAnswer str = horpo.run(trs);
    assertTrue(str.status(trs.lookupSymbol("f")).equals("Mul_2"));
  }

  @Test
  public void testMulFailureWithTWo() {
    TRS trs = makeTrs("f :: Int -> Int -> unit\n" +
                      "f(x, y) -> f(y-1, x + 1) | x > 0 ∧ y > 0\n");
    Horpo horpo = new Horpo(trs);
    assertTrue(horpo.run(trs) == null);
  }

  @Test
  public void testMulWithLowerArgumentCountLeft() {
    TRS trs = makeTrs("f :: Int -> Int -> Int -> unit\n" +
                      "g :: (Int -> unit) -> unit\n" +
                      "g(f(x, y)) -> f(y-1, x, y - 2) | x > 0 ∧ y > 0\n" +
                      "f(x, y, z) -> f(z, x, y-1) | y > -12\n");
    Horpo horpo = new Horpo(trs);
    Horpo.HorpoAnswer answer = horpo.run(trs);
    assertTrue(answer.status(trs.lookupSymbol("f")).equals("Mul_3"));
  }

  @Test
  public void testMulWithLowerArgumentCountRight() {
    TRS trs = makeTrs("f :: Int -> Int -> Int -> unit\n" +
                      "g :: (Int -> unit) -> unit\n" +
                      "f(x, y, z) -> g(f(y-1, x)) | y > 0\n");
    Horpo horpo = new Horpo(trs);
    Horpo.HorpoAnswer answer = horpo.run(trs);
    assertTrue(answer.status(trs.lookupSymbol("f")).equals("Mul_2"));
  }

  @Test
  public void testMulWithLowerArgumentCountRightNotPossible() {
    TRS trs = makeTrs("f :: Int -> Int -> Int -> unit\n" +
                      "g :: (Int -> unit) -> unit\n" +
                      "f(x, y, z) -> g(f(y-1, x)) | y > 0\n" +
                      "f(x, y, z) -> f(z, x, y-1) | y > -12\n");
    Horpo horpo = new Horpo(trs);
    Horpo.HorpoAnswer answer = horpo.run(trs);
    assertTrue(answer == null);
  }
  */
}

