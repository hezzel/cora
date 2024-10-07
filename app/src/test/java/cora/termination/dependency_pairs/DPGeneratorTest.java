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

package cora.termination.dependency_pairs;

import charlie.terms.FunctionSymbol;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;

class DPGeneratorTest {
  @Test
  public void generateDPsWithOneSimpleTailRecursiveRule() {
    TRS trs = CoraInputReader.readTrsFromString(
      "eval :: Int -> Int -> Int\n" +
      "eval(x, y) -> eval(x - 1, y) | x > y\n");
    DPGenerator generator = new DPGenerator(trs);
    assertTrue(generator.queryDPSort().name().equals("dpsort"));
    FunctionSymbol evalsharp = generator.querySharpSymbolFor(trs.lookupSymbol("eval")).get();
    assertTrue(evalsharp.queryType().toString().equals("Int → Int → dpsort"));
    assertTrue(evalsharp.queryName().equals("eval#"));
    Problem prob = generator.queryProblem(true, false);
    assertTrue(prob.isInnermost());
    assertFalse(prob.hasExtraRules());
    assertFalse(prob.hasPrivateDPs());
    assertTrue(prob.queryTerminationStatus().equals(Problem.TerminationFlag.Computable));
    assertFalse(prob.getOriginalTRS() == trs);
    assertTrue(prob.getOriginalTRS().lookupSymbol("eval#") == evalsharp);
    assertTrue(trs.lookupSymbol("eval#") == null);
    assertTrue(prob.getDPList().size() == 1);
    assertTrue(prob.getDPList().get(0).ustr().equals(
      "eval#(x, y) => eval#(x - 1, y) | x > y { }"));
  }

  @Test
  public void generateDPsWithGeneralRecursiveRule() {
    TRS trs = CoraInputReader.readTrsFromString(
      "cons :: Int -> list -> list\n" +
      "nil :: list\n" +
      "append :: list -> list -> list\n" +
      "append(cons(x,y), z) -> cons(x, append(y,z))\n");
    DPGenerator generator = new DPGenerator(trs);
    Problem prob = generator.queryProblem(false, false);
    assertFalse(prob.isInnermost());
    assertFalse(prob.hasExtraRules());
    assertTrue(prob.getDPList().size() == 1);
    assertTrue(prob.getDPList().get(0).ustr().equals(
      "append#(cons(x, y), z) => append#(y, z) | true { }"));
  }

  @Test
  public void generateDPsWithPartiallyAppliedRule() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "private g :: (Int -> Int) -> Int -> Int\n" +
      "g(F,y) -> F(y)\n" +
      "f(x) -> g(f(x-1)) | x > 0\n");
    DPGenerator generator = new DPGenerator(trs);
    Problem prob = generator.queryProblem(true, true);
    assertTrue(prob.isInnermost());
    assertTrue(prob.hasExtraRules());
    assertFalse(prob.hasPrivateDPs());
    assertTrue(prob.getOriginalTRS().lookupSymbol("f#").queryType().toString().equals(
      "Int → Int → dpsort"));
    assertTrue(prob.getDPList().size() == 2);
    assertTrue(prob.getDPList().get(0).ustr().equals(
      "f#(x, arg2) => f#(x - 1, fresh1) | x > 0 { }"));
    assertTrue(prob.getDPList().get(1).ustr().equals(
      "f#(x, arg2) => g#(f(x - 1), arg2) | x > 0 { }"));
  }

  @Test
  public void generateDPsWithHigherOrderRule() {
    TRS trs = CoraInputReader.readTrsFromString(
      "nil :: list\n" +
      "cons :: Int -> list -> list\n" +
      "private map :: (Int -> Int) -> list -> list\n" +
      "start :: list -> list\n" +
      "map(F, nil) -> nil\n" +
      "map(F, cons(x, y)) -> cons(F(x), map(F, y))\n" +
      "start -> map([+](2))\n"
    );
    DPGenerator generator = new DPGenerator(trs);
    Problem prob = generator.queryProblem(false, true);
    assertFalse(prob.isInnermost());
    assertTrue(prob.hasExtraRules());
    assertTrue(prob.hasPrivateDPs());
    assertTrue(prob.getDPList().size() == 2);
    assertTrue(prob.getDPList().get(0).lhs().queryRoot().queryType().toString().equals(
      "(Int → Int) → list → dpsort"));
    assertTrue(prob.isPrivate(0));
    assertFalse(prob.isPrivate(1));
    assertTrue(prob.getDPList().get(0).ustr().equals(
      "map#(F, cons(x, y)) => map#(F, y) | true { }"));
    assertTrue(prob.getDPList().get(1).ustr().equals(
      "start#(arg1) => map#([+](2), arg1) | true { }"));
  }

  @Test
  public void testProductTypeTransformation() {
    TRS trs = CoraInputReader.readTrsFromString(
      "swap :: (| a , b |) -> (| b, a |)\n" +
      "swap( (| x, y |) ) -> id( (| y, x |) )\n" +
      "id :: (| b, a |) -> (| b, a |)\n" +
      "id(x) -> x\n"
    );
    DPGenerator generator = new DPGenerator(trs);
    Problem prob = generator.queryProblem(false, true);
    assertTrue(prob.getDPList().size() == 1);
    FunctionSymbol swapsharp = generator.querySharpSymbolFor(trs.lookupSymbol("swap")).get();
    assertTrue(swapsharp.queryName().equals("swap#"));
    assertTrue(swapsharp.queryType().toString().equals("⦇ a, b ⦈ → dpsort"));
  }

  @Test
  public void testSharpNameAlreadyTaken() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> A\n" +
      "f# :: Int -> A\n" +
      "f(x) -> f#(x)\n"
    );
    DPGenerator generator = new DPGenerator(trs);
    assertTrue(generator.querySharpSymbolFor(trs.lookupSymbol("f")).get()
      .queryName().equals("f#1"));
  }

  @Test
  public void testSharpNameReplacementAlsoTaken() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> A\n" +
      "f# :: Int -> A\n" +
      "f#1 :: Int -> A\n" +
      "f(x) -> f#(x)\n" +
      "f#(x) -> f#1(x)\n" +
      "f#1(x) -> f(x)\n"
    );
    DPGenerator generator = new DPGenerator(trs);
    assertTrue(generator.querySharpSymbolFor(trs.lookupSymbol("f")).get()
      .queryName().equals("f#2"));
  }

  @Test
  public void chooseDifferentDPSort() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> A\n" +
      "wrap :: A -> A\n" +
      "f# :: Int -> dpsort\n" +
      "f(x) -> wrap(f(x-1)) | x > 0\n" +
      "f#(x) -> f#(x-1) | x > 0\n");
    DPGenerator generator = new DPGenerator(trs);
    assertTrue(generator.queryDPSort().toString().equals("DPSORT"));
  }

  @Test
  public void chooseNumberedDPSort() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> A\n" +
      "wrap :: A -> A\n" +
      "tmp1 :: DPSORT\n" +
      "tmp2 :: dp_sort\n" +
      "tmp3 :: DP_SORT\n" +
      "tmp4 :: dpsort1\n" +
      "f# :: Int -> dpsort\n" +
      "f(x) -> wrap(f(x-1)) | x > 0\n" +
      "f#(x) -> f#(x-1) | x > 0\n");
    DPGenerator generator = new DPGenerator(trs);
    assertTrue(generator.queryDPSort().toString().equals("dpsort2"));
  }
}
