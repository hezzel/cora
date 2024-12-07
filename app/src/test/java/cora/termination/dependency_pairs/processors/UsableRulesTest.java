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

package cora.termination.dependency_pairs.processors;

import charlie.util.FixedList;
import charlie.terms.FunctionSymbol;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.trs.TrsFactory;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.DP;

import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class UsableRulesTest {
  private String getMessage(TRS trs, ProcessorProofObject po) {
    OutputModule module = DefaultOutputModule.createUnicodeModule(trs);
    po.justify(module);
    return module.toString();
  }

  @Test
  void testComputeURWithoutRecursion() {
    UsableRulesProcessor proc = new UsableRulesProcessor();
    TRS trs = CoraInputReader.readTrsFromString(
      "minus :: Int -> Int -> Int\n" +
      "minus(x, y) -> x - y | x ≥ y\n" +
      "minus(x, y) -> 0 | x < y\n" +
      "quot :: Int -> Int -> Int\n" +
      "quot(0, 1) -> 0\n" +
      "quot(x, y) -> 1 + quot(minus(x,y), y) | x > 0 ∧ y > 0\n" +
      "nil :: List\n" +
      "cons :: Int -> List -> List\n" +
      "map :: (Int -> Int) -> List -> List\n" +
      "map(F, nil) -> nil\n" +
      "map(F, cons(x,y)) -> cons(F(x), map(F, y))\n" +
      "helper :: Int -> Int\n" +
      "helper(x) -> quot(x, 2)\n" +
      "start :: List -> List\n" +
      "start -> map(helper)\n",
      TrsFactory.LCSTRS
    );
    Problem prob = (new DPGenerator(trs)).queryProblem(true, true);
    assertTrue(proc.isApplicable(prob));
    assertTrue(proc.printUsableSymbols(prob).equals("(helper,0) (minus,2) "));
    // we do NOT get quot as usable symbol, because the helper rule takes more than 0 arguments!
    
    ProcessorProofObject po = proc.processDPP(prob);
    assertTrue(po.applicable());
    assertTrue(po.queryResults().size() == 1);
    FixedList<Rule> result = po.queryOutput().getRuleList();
    assertTrue(result.size() == 2);
    assertTrue(result.get(0).toString().equals("minus(x, y) → x - y | x ≥ y"));
    assertTrue(result.get(1).toString().equals("minus(x, y) → 0 | x < y"));
    assertTrue(getMessage(trs, po).equals(
      "We obtain 2 usable rules (out of 8 rules in the input problem).\n\n"));
  }

  private TRS exampleTRS() {
    return CoraInputReader.readTrsFromString(
      "0 :: nat\n" +
      "s :: nat -> nat\n" +
      "fact :: nat -> nat\n" +
      "fact(0) -> s(0)\n" +
      "fact(s(x)) -> mul(s(x), fact(x))\n" +
      "mul :: nat -> nat -> nat\n" +
      "mul(0, x) -> 0\n" +
      "mul(s(y), x) -> id(add(x, mul(x, y)))\n" +
      "id :: nat -> nat\n" +
      "id -> id2\n" +
      "id2 :: nat -> nat\n" +
      "id2(x) -> x\n" +
      "add :: nat -> nat -> nat\n" +
      "add(0, y) -> y\n" +
      "add(s(x), y) -> s(add(y, x))\n",
      TrsFactory.STRS
    );
  }

  @Test
  void testComputeURWithRecursion() {
    UsableRulesProcessor proc = new UsableRulesProcessor();
    TRS trs = exampleTRS();
    Problem prob = (new DPGenerator(trs)).queryProblem(true, false);
    assertTrue(proc.isApplicable(prob));
    assertTrue(proc.printUsableSymbols(prob).equals("(add,2) (fact,1) (id2,1) (id,1) (mul,2) "));
    ProcessorProofObject po = proc.processDPP(prob);
    assertTrue(po.applicable());
    assertTrue(getMessage(trs, po).equals(
      "We obtain 8 usable rules (out of 8 rules in the input problem).\n\n"));
    // note that NOT all the original rules are usable: the id rule is actually adapted:
    assertTrue(po.queryOutput().getRuleList().get(5).toString().equals("id(arg2) → id2(arg2)"));
  }

  @Test
  public void testComputeURWithOnlyPartUsable() {
    UsableRulesProcessor proc = new UsableRulesProcessor();
    TRS trs = exampleTRS();
    Problem prob = (new DPGenerator(trs)).queryProblem(true, false);
    prob = prob.removeDPs(Set.of(0, 1, 2, 3, 5, 6), true); // only leave the mul# -> id# rule
    assertTrue(proc.isApplicable(prob));
    assertTrue(proc.printUsableSymbols(prob).equals("(add,2) (id2,1) (id,1) (mul,2) "));

    ProcessorProofObject po = proc.processDPP(prob);
    assertTrue(po.queryOutput().getRuleList().size() == 6);
    assertTrue(getMessage(trs, po).equals(
      "We obtain 6 usable rules (out of 8 rules in the input problem).\n\n"));
  }

  @Test
  public void testComputeURWithPartialApplication() {
    UsableRulesProcessor proc = new UsableRulesProcessor();
    TRS trs = CoraInputReader.readTrsFromString(
      "h :: (Int -> Int) -> Int -> Int\n" +
      "f :: (Int -> Int) -> Int -> Int\n" +
      "g :: (Int -> Int) -> Int -> Int\n" +
      "h(F, y) -> h(f(F), y - 1) | y > 0\n" +
      "f -> g\n" +
      "g(F, y) -> F(y+1)\n" +
      "a :: Int\n" +
      "b :: (Int -> Int) -> Int -> Int\n" +
      "c :: Int -> Int\n" +
      "d :: Int -> Int\n" +
      "a -> b(c, c(0))\n" +
      "b(x,y) -> y\n" +
      "c -> d\n",
      TrsFactory.LCSTRS
    );
    Problem prob = (new DPGenerator(trs)).queryProblem(true, true);
    assertTrue(proc.printUsableSymbols(prob).equals("(c,0) (c,1) (f,1) (g,1) "));
    ProcessorProofObject po = proc.processDPP(prob);
    assertTrue(po.queryOutput().getRuleList().size() == 2);
      // the only g rule takes two arguments, so is not included
    assertTrue(po.queryOutput().getRuleList().get(0).toString().equals("c → d"));
    assertTrue(po.queryOutput().getRuleList().get(1).toString().equals("f(arg2) → g(arg2)"));
    assertTrue(getMessage(trs, po).equals(
      "We obtain 2 usable rules (out of 6 rules in the input problem).\n\n"));
  }

  @Test
  public void testIllegalVartermInDPs() {
    UsableRulesProcessor proc = new UsableRulesProcessor();
    TRS trs = CoraInputReader.readTrsFromString(
      "rec :: (A -> A) -> A -> Int -> A\n" +
      "rec(F, x, n) -> x | n <= 0\n" +
      "rec(F, x, n) -> rec(F, F(x), n-1) | n > 0\n",
      TrsFactory.LCSTRS
    );
    Problem prob = (new DPGenerator(trs)).queryProblem(true, false);
    assertTrue(proc.printUsableSymbols(prob).equals("NA"));
    ProcessorProofObject po = proc.processDPP(prob);
    assertFalse(po.applicable());
    assertTrue(getMessage(trs, po).equals("The Usable Rules method is not applicable.\n\n"));
  }

  @Test
  public void testIllegalVartermInUsableRule() {
    UsableRulesProcessor proc = new UsableRulesProcessor();
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: (Int -> Int) -> Int -> A\n" +
      "g :: (Int -> Int) -> Int -> Int\n" +
      "h :: Int -> Int\n" +
      "f(F, x) -> f(F, g(F,x-1)) | x > 0\n" +
      "g(F, x) -> h(F(0) + x)\n",
      TrsFactory.LCSTRS
    );
    Problem prob = (new DPGenerator(trs)).queryProblem(true, false);
    assertTrue(proc.printUsableSymbols(prob).equals("NA"));
    assertFalse(proc.processDPP(prob).applicable());
  }

  @Test
  public void testIllegalRighthandVar() {
    UsableRulesProcessor proc = new UsableRulesProcessor();
    TRS trs = CoraInputReader.readTrsFromString(
      "cons :: (Int -> Int) -> list -> list\n" +
      "a :: list -> Int\n" +
      "b :: Int -> Int\n" +
      "hd :: list -> Int -> Int\n" +
      "hd(cons(F,xs)) -> F\n" +
      "a(lst) -> b(hd(lst, 0))\n" +
      "b(x) -> x\n",
      TrsFactory.LCSTRS
    );
    Problem prob = (new DPGenerator(trs)).queryProblem(true, true);
    assertTrue(proc.printUsableSymbols(prob).equals("NA"));
    assertFalse(proc.processDPP(prob).applicable());
  }

  @Test
  public void testEverythingUsableNoChanges() {
    UsableRulesProcessor proc = new UsableRulesProcessor();
    TRS trs = CoraInputReader.readTrsFromString(
      "0 :: nat\n" +
      "s :: nat -> nat\n" +
      "fact :: nat -> nat\n" +
      "fact(0) -> s(0)\n" +
      "fact(s(x)) -> mul(s(x), fact(x))\n" +
      "mul :: nat -> nat -> nat\n" +
      "mul(0, x) -> 0\n" +
      "mul(s(y), x) -> id(add(x, mul(x, y)))\n" +
      "id :: nat -> nat\n" +
      "id(x) -> x\n" +
      "add :: nat -> nat -> nat\n" +
      "add(0, y) -> y\n" +
      "add(s(x), y) -> s(add(y, x))\n",
      TrsFactory.STRS
    );

    DPGenerator generator = new DPGenerator(trs);
    Problem prob1 = generator.queryProblem(true, true);
    ProcessorProofObject po1 = proc.processDPP(prob1);
    assertTrue(po1.applicable());
    assertTrue(getMessage(trs, po1).equals("All known rules are usable, but the Usable Rules " +
      "method is applicable so the extra rules are not usable, and may be dropped.\n\n"));
    assertTrue(po1.queryOutput().getDPList() == prob1.getDPList());
    assertTrue(po1.queryOutput().getRuleList() == prob1.getRuleList());
    assertTrue(po1.queryOutput().isInnermost());
    assertFalse(po1.queryOutput().hasExtraRules());

    Problem prob2 = generator.queryProblem(true, false);
    ProcessorProofObject po2 = proc.processDPP(prob2);
    assertFalse(po2.applicable());
    assertTrue(getMessage(trs, po2).equals("All rules are usable.\n\n"));
    assertTrue(po2.queryOutput() == prob2);
  }
}

