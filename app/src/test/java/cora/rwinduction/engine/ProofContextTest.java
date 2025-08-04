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

package cora.rwinduction.engine;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;
import java.util.Set;

import charlie.terms.*;
import charlie.trs.*;
import charlie.reader.CoraInputReader;

class ProofContextTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "sum1 :: Int -> Int\n" +
      "sum1(y) -> 0 | y <= 0\n" +
      "sum1(x) -> x + sum1(x-1) | x > 0\n" +
      "sum2 :: Int -> Int\n" +
      "sum2(x) -> iter(x, 0, 0)\n" +
      "iter :: Int -> Int -> Int -> Int\n" +
      "iter(x, i, z) -> z | i > x\n" +
      "iter(x, i, z) -> iter(x, i+1, z+i) | i <= x\n" +
      "o :: nat\n" +
      "s :: nat -> nat\n" +
      "add :: (| nat , nat |) -> nat\n" +
      "add( (|x, o|) ) -> x\n" +
      "add( (|x, s(y) |) ) -> add( (| s(x),y |) )\n" +
      "something :: Int -> Int -> (| Bool , Int |)\n" +
      "partial :: Int -> Int -> Int\n" +
      "partial(x) -> sum1\n"
    );
  }

  @Test
  public void testConstructors() {
    TRS trs = setupTRS();
    ProofContext context = new ProofContext(trs, lst -> new Renaming(Set.of()));
    assertTrue(context.getConstructors(CoraInputReader.readType("Int")).isEmpty());
    assertTrue(context.getConstructors(CoraInputReader.readType("Bool")).isEmpty());
    Set<FunctionSymbol> funcs = context.getConstructors(CoraInputReader.readType("nat"));
    assertTrue(funcs.size() == 2);
    assertTrue(funcs.contains(trs.lookupSymbol("o")));
    assertTrue(funcs.contains(trs.lookupSymbol("s")));
    assertFalse(funcs.contains(trs.lookupSymbol("add")));
    funcs = context.getConstructors(CoraInputReader.readType("(|Bool,Int|)"));
    assertTrue(funcs.size() == 1);
  }

  @Test
  public void testRuleArity() {
    TRS trs = setupTRS();
    ProofContext context = new ProofContext(trs, lst -> new Renaming(Set.of()));
    assertTrue(context.queryRuleArity(trs.lookupSymbol("o")) == 1);
    assertTrue(context.queryRuleArity(trs.lookupSymbol("something")) == 3);
    assertTrue(context.queryRuleArity(trs.lookupSymbol("add")) == 1);
    assertTrue(context.queryRuleArity(trs.lookupSymbol("iter")) == 3);
    assertTrue(context.queryRuleArity(trs.lookupSymbol("partial")) == 1);
    assertTrue(context.queryRuleArity(TheoryFactory.plusSymbol) == 2);
    assertTrue(context.queryRuleArity(TheoryFactory.minusSymbol) == 1);
  }

  @Test
  public void testVariableNamer() {
    TRS trs = setupTRS();
    TermPrinter printer = new TermPrinter(Set.of());
    ProofContext context = new ProofContext(trs, lst -> printer.generateUniqueNaming(lst));
    VariableNamer namer = context.getVariableNamer();
    assertTrue(namer.queryDefaultNaming(trs.lookupSymbol("sum1"), 1) == null);
    assertTrue(namer.queryDefaultNaming(trs.lookupSymbol("sum2"), 1).equals("x"));
    assertTrue(namer.queryDefaultNaming(trs.lookupSymbol("sum2"), 2) == null);
    assertTrue(namer.queryDefaultNaming(trs.lookupSymbol("iter"), 1).equals("x"));
    assertTrue(namer.queryDefaultNaming(trs.lookupSymbol("iter"), 2).equals("i"));
    assertTrue(namer.queryDefaultNaming(trs.lookupSymbol("iter"), 3).equals("z"));
    assertTrue(namer.queryDefaultNaming(trs.lookupSymbol("add"), 1) == null);
    assertTrue(namer.queryDefaultNaming(trs.lookupSymbol("s"), 1).equals("y"));
  }

  @Test
  public void testVariableNamerWithDuplicateName() {
    // create the TRS with one rule: f(x__1, x__2) -> f(x__1, x__2)
    Variable x1 = TermFactory.createVar("x", CoraInputReader.readType("Int"));
    Variable x2 = TermFactory.createVar("x", CoraInputReader.readType("Int"));
    FunctionSymbol f = TermFactory.createConstant("f", CoraInputReader.readType("Int -> Int -> A"));
    Term s = f.apply(x1).apply(x1);
    Rule rule = TrsFactory.createRule(s, s);
    Alphabet alphabet = new Alphabet(Set.of(f));
    TRS trs = TrsFactory.createTrs(alphabet, List.of(rule), TrsFactory.MSTRS);
    // create a proof context, and see the variable namer it creates
    TermPrinter printer = new TermPrinter(Set.of("f"));
    ProofContext context = new ProofContext(trs, lst -> printer.generateUniqueNaming(lst));
    VariableNamer namer = context.getVariableNamer();
    // make sure those variables are still called x!
    assertTrue(namer.queryDefaultNaming(f, 1).equals("x"));
    assertTrue(namer.queryDefaultNaming(f, 2).equals("x"));
  }
}

