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

package cora.termination.dependency_pairs.processors.redpair;

import charlie.trs.TRS;
import charlie.trs.TrsFactory;
import charlie.smt.SmtProblem;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.termination.reduction_pairs.*;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.processors.Processor;

import java.util.Set;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class URWrtRedPairProcessorTest {
  private TRS exampleTRS() {
    return CoraInputReader.readTrsFromString(
      "0 :: nat\n" +
      "s :: nat -> nat\n" +
      "true :: bool\n" +
      "false :: bool\n" +
      "min :: nat -> nat -> nat\n" +
      "min(x,0) -> x\n" +
      "min(s(x), s(y)) -> min(x,y)\n" +
      "quot :: nat -> nat -> nat\n" +
      "quot(0, s(y)) -> 0\n" +
      "quot(s(x), s(y)) -> s(quot(min(x,y), s(y)))\n" +
      "leq :: nat -> nat -> bool\n" +
      "leq(0,y) -> true\n" +
      "leq(s(x),0) -> false\n" +
      "leq(s(x),s(y)) -> leq(x,y)\n" +
      "sma :: bool -> (nat -> bool) -> nat -> nat\n" +
      "sma(b,F,0) -> 0\n" +
      "sma(true, F, s(x)) -> s(x)\n" +
      "sma(false, F, s(x)) -> sma(F(x), F, quot(x, s(s(0))))\n" +
      "start :: nat -> nat -> nat\n" +
      "start(0,m) -> m\n" +
      "start(s(n),m) -> start(n,sma(false, leq(m), n))\n",
      TrsFactory.STRS
    );
  }

  private Problem exampleProblem() {
    Problem prob = (new DPGenerator(exampleTRS())).queryProblem(true, true);
    return prob.removeDPs(Set.of(0,1,2,3,4,6,7), true);
  }

  private class MyRedPair implements ReductionPair {
    private String _oprob;
    private String _smt;
    public boolean isStronglyMonotonic() { return false; }
    public boolean isApplicable(OrderingProblem oprob) { return true; }
    public String queryName() { return "MyRedPair"; }
    public ReductionPairProofObject solve(OrderingProblem oprob, SmtProblem smt) {
      _oprob = oprob.toString();
      _smt = smt.toString();
      return new ReductionPairProofObject(oprob) {
        public void justify(OutputModule module) {}
      };
    }
  }

  @Test
  public void testUnconstrainedData() {
    Problem oprob = exampleProblem();
    MyRedPair mrp = new MyRedPair();
    Processor proc = new URWrtRedPairProcessor(mrp);
    proc.processDPP(oprob);
    assertTrue(mrp._oprob.toString().equals(
      "C) [usable_{min2}]  ==>  min2(x, 00) Weak x | true {[] }\n" +
      "C) [usable_{min2}]  ==>  min2(s1(x), s1(y)) Weak min2(x, y) | true {[] }\n" +
      "C) [usable_{quot2}]  ==>  quot2(00, s1(y)) Weak 00 | true {[] }\n" +
      "C) [usable_{quot2}]  ==>  quot2(s1(x), s1(y)) Weak s1(quot2(min2(x, y), s1(y))) | true {[] }\n" +
      "C) [usable_{leq2}]  ==>  leq2(00, y) Weak true0 | true {[] }\n" +
      "C) [usable_{leq2}]  ==>  leq2(s1(x), 00) Weak false0 | true {[] }\n" +
      "C) [usable_{leq2}]  ==>  leq2(s1(x), s1(y)) Weak leq2(x, y) | true {[] }\n" +
      "C) [usable_{sma3}]  ==>  sma3(b, F, 00) Weak 00 | true {[] }\n" +
      "C) [usable_{sma3}]  ==>  sma3(true0, F, s1(x)) Weak s1(x) | true {[] }\n" +
      "C) [usable_{sma3}]  ==>  sma3(false0, F, s1(x)) Weak sma3($, F, quot2(x, s1(s1(00)))) | true {[] }\n" +
      "C) [usable_{start2}]  ==>  start2(00, m) Weak m | true {[] }\n" +
      "C) [usable_{start2}]  ==>  start2(s1(n), m) Weak start2(n, sma3(false0, leq1(m), n)) | true {[] }\n" +
      "E) 0  :  sma#3(false0, F, s1(x)) Strict sma#3($, F, quot2(x, s1(s1(00)))) | true {[] }\n" +
      "E) 1  :  start#2(s1(n), m) Strict start#2(n, sma3(false0, leq1(m), n)) | true {[] }\n"));

    assertTrue(mrp._smt.equals(
      // all the regards equivalences
      "![regards{leq,1}] or [regards{leq1,1}]\n" +
      "![regards{leq1,1}] or [regards{leq,1}]\n" +
      "![regards{leq,1}] or [regards{leq2,1}]\n" +
      "![regards{leq2,1}] or [regards{leq,1}]\n" +
      "![regards{leq,2}] or [regards{leq2,2}]\n" +
      "![regards{leq2,2}] or [regards{leq,2}]\n" +
      "![regards{min,1}] or [regards{min2,1}]\n" +
      "![regards{min2,1}] or [regards{min,1}]\n" +
      "![regards{min,2}] or [regards{min2,2}]\n" +
      "![regards{min2,2}] or [regards{min,2}]\n" +
      "![regards{quot,1}] or [regards{quot2,1}]\n" +
      "![regards{quot2,1}] or [regards{quot,1}]\n" +
      "![regards{quot,2}] or [regards{quot2,2}]\n" +
      "![regards{quot2,2}] or [regards{quot,2}]\n" +
      "![regards{sma#,1}] or [regards{sma#3,1}]\n" +
      "![regards{sma#3,1}] or [regards{sma#,1}]\n" +
      "![regards{sma#,2}] or [regards{sma#3,2}]\n" +
      "![regards{sma#3,2}] or [regards{sma#,2}]\n" +
      "![regards{sma#,3}] or [regards{sma#3,3}]\n" +
      "![regards{sma#3,3}] or [regards{sma#,3}]\n" +
      "![regards{sma,1}] or [regards{sma3,1}]\n" +
      "![regards{sma3,1}] or [regards{sma,1}]\n" +
      "![regards{sma,2}] or [regards{sma3,2}]\n" +
      "![regards{sma3,2}] or [regards{sma,2}]\n" +
      "![regards{sma,3}] or [regards{sma3,3}]\n" +
      "![regards{sma3,3}] or [regards{sma,3}]\n" +
      "![regards{start#,1}] or [regards{start#2,1}]\n" +
      "![regards{start#2,1}] or [regards{start#,1}]\n" +
      "![regards{start#,2}] or [regards{start#2,2}]\n" +
      "![regards{start#2,2}] or [regards{start#,2}]\n" +
      "![regards{start,1}] or [regards{start2,1}]\n" +
      "![regards{start2,1}] or [regards{start,1}]\n" +
      "![regards{start,2}] or [regards{start2,2}]\n" +
      "![regards{start2,2}] or [regards{start,2}]\n" +
      "![regards{s,1}] or [regards{s1,1}]\n" +
      "![regards{s1,1}] or [regards{s,1}]\n" +
      // usable symbols for the dependency pairs
      "![regards{sma#3,1}]\n" +
      "![regards{sma#3,3}] or [usable_{quot2}]\n" +
      "![regards{start#2,2}] or [usable_{sma3}]\n" +
      // usable symbols for the rules
      "![usable_{quot2}] or ![regards{s1,1}] or ![regards{quot2,1}] or [usable_{min2}]\n" +
      "![usable_{sma3}] or ![regards{sma3,1}]\n" +
      "![usable_{sma3}] or ![regards{sma3,3}] or [usable_{quot2}]\n" +
      "![usable_{start2}] or ![regards{start2,2}] or [usable_{sma3}]\n"));
  }

  private TRS exampleTRS2() {
    return CoraInputReader.readTrsFromString(
      "nil :: list\n" +
      "cons :: A -> list -> list\n" +
      "skip :: Int -> list -> list\n" +
      "skip(k, nil) -> nil\n" +
      "skip(k, ys) -> ys | k <= 0\n" +
      "skip(k, cons(x, ys)) -> skip(k-1+(k-k), ys) | k > 0\n" +
      "skipfold :: (A -> B -> B) -> B -> Int -> list -> B\n" +
      "skipfold(F, n, k, nil) -> n\n" +
      "skipfold(F, n, k, cons(x, ys)) -> skipfold(F, F(x, n), k, skip(k, ys))\n" +
      "id :: Int -> Int\n" +
      "id(x) -> x\n" +
      "test :: Int -> Int\n" +
      "test(x) -> x * x\n" +  // theory term with variables NOT in a constraint
      "recurse :: Int -> Int\n" +
      "recurse(x) -> recurse(x + id(-1)) | x > 0\n",
      TrsFactory.LCSTRS);
  }

  private Problem exampleProblem2() {
    Problem prob = (new DPGenerator(exampleTRS2())).queryProblem(true, false);
    return prob.removeDPs(Set.of(0,1,3), true);
  }

  @Test
  public void testConstrainedData() {
    Problem oprob = exampleProblem2();
    MyRedPair mrp = new MyRedPair();
    Processor proc = new URWrtRedPairProcessor(mrp);
    proc.processDPP(oprob);
    assertTrue(mrp._oprob.toString().equals(
      "C) [usable_{skip2}]  ==>  skip2(k, nil0) Weak nil0 | true {[] }\n" +
      "C) [usable_{skip2}]  ==>  skip2(k, ys) Weak ys | k ≤ 0 {[k] }\n" +
      "C) [usable_{skip2}]  ==>  skip2(k, cons2(x, ys)) Weak skip2(k - 1 + (k - k), ys) | k > 0 {[k] }\n" +
      "C) [usable_{skipfold4}]  ==>  skipfold4(F, n, k, nil0) Weak n | true {[] }\n" +
      "C) [usable_{skipfold4}]  ==>  skipfold4(F, n, k, cons2(x, ys)) Weak skipfold4(F, $, k, skip2(k, ys)) | true {[] }\n" +
      "C) [usable_{id1}]  ==>  id1(x) Weak x | true {[] }\n" +
      "C) [usable_{test1}]  ==>  test1(x) Weak *2(x, x) | true {[] }\n" +
      "C) [usable_{recurse1}]  ==>  recurse1(x) Weak recurse1(+2(x, id1(-1))) | x > 0 {[x] }\n" +
      // potential usable rules for * and + are included, but NOT for - as it only occurs in a full theory position
      "C) [usable_{*2}]  ==>  *2(x1, x2) Weak y | y = x1 * x2 {[x1, x2, y] }\n" +
      "C) [usable_{+2}]  ==>  +2(x1, x2) Weak y | y = x1 + x2 {[x1, x2, y] }\n" +
      "E) 0  :  skipfold#4(F, n, k, cons2(x, ys)) Strict skipfold#4(F, $, k, skip2(k, ys)) | true {[] }\n" +
      "E) 1  :  recurse#1(x) Strict recurse#1(+2(x, id1(-1))) | x > 0 {[x] }\n"));

    assertTrue(mrp._smt.toString().equals(
      // regards({f,i) <--> regards{f_n,i} if i ≤ n
      "![regards{*,1}] or [regards{*2,1}]\n" +
      "![regards{*2,1}] or [regards{*,1}]\n" +
      "![regards{*,2}] or [regards{*2,2}]\n" +
      "![regards{*2,2}] or [regards{*,2}]\n" +
      "![regards{+,1}] or [regards{+2,1}]\n" +
      "![regards{+2,1}] or [regards{+,1}]\n" +
      "![regards{+,2}] or [regards{+2,2}]\n" +
      "![regards{+2,2}] or [regards{+,2}]\n" +
      "![regards{cons,1}] or [regards{cons2,1}]\n" +
      "![regards{cons2,1}] or [regards{cons,1}]\n" +
      "![regards{cons,2}] or [regards{cons2,2}]\n" +
      "![regards{cons2,2}] or [regards{cons,2}]\n" +
      "![regards{id,1}] or [regards{id1,1}]\n" +
      "![regards{id1,1}] or [regards{id,1}]\n" +
      "![regards{recurse#,1}] or [regards{recurse#1,1}]\n" +
      "![regards{recurse#1,1}] or [regards{recurse#,1}]\n" +
      "![regards{recurse,1}] or [regards{recurse1,1}]\n" +
      "![regards{recurse1,1}] or [regards{recurse,1}]\n" +
      "![regards{skipfold#,1}] or [regards{skipfold#4,1}]\n" +
      "![regards{skipfold#4,1}] or [regards{skipfold#,1}]\n" +
      "![regards{skipfold#,2}] or [regards{skipfold#4,2}]\n" +
      "![regards{skipfold#4,2}] or [regards{skipfold#,2}]\n" +
      "![regards{skipfold#,3}] or [regards{skipfold#4,3}]\n" +
      "![regards{skipfold#4,3}] or [regards{skipfold#,3}]\n" +
      "![regards{skipfold#,4}] or [regards{skipfold#4,4}]\n" +
      "![regards{skipfold#4,4}] or [regards{skipfold#,4}]\n" +
      "![regards{skipfold,1}] or [regards{skipfold4,1}]\n" +
      "![regards{skipfold4,1}] or [regards{skipfold,1}]\n" +
      "![regards{skipfold,2}] or [regards{skipfold4,2}]\n" +
      "![regards{skipfold4,2}] or [regards{skipfold,2}]\n" +
      "![regards{skipfold,3}] or [regards{skipfold4,3}]\n" +
      "![regards{skipfold4,3}] or [regards{skipfold,3}]\n" +
      "![regards{skipfold,4}] or [regards{skipfold4,4}]\n" +
      "![regards{skipfold4,4}] or [regards{skipfold,4}]\n" +
      "![regards{skip,1}] or [regards{skip2,1}]\n" +
      "![regards{skip2,1}] or [regards{skip,1}]\n" +
      "![regards{skip,2}] or [regards{skip2,2}]\n" +
      "![regards{skip2,2}] or [regards{skip,2}]\n" +
      "![regards{test,1}] or [regards{test1,1}]\n" +
      "![regards{test1,1}] or [regards{test,1}]\n" +
      "![regards{skipfold#4,2}]\n" +
      // usability requirements
      "![regards{skipfold#4,4}] or [usable_{skip2}]\n" +
      "![regards{recurse#1,1}] or [usable_{+2}]\n" +
      "![regards{recurse#1,1}] or ![regards{+2,2}] or [usable_{id1}]\n" +
      "![usable_{skipfold4}] or ![regards{skipfold4,2}]\n" +
      "![usable_{skipfold4}] or ![regards{skipfold4,4}] or [usable_{skip2}]\n" +
      "![usable_{test1}] or [usable_{*2}]\n" +
      "![usable_{recurse1}] or ![regards{recurse1,1}] or [usable_{+2}]\n" +
      "![usable_{recurse1}] or ![regards{recurse1,1}] or ![regards{+2,2}] or [usable_{id1}]\n"));
  }

  private TRS exampleTRS3() {
    return CoraInputReader.readTrsFromString(
      "f :: Int -> (Int -> Int) -> Int -> Int\n" +
      "f(x) -> g(x)\n" +
      "g :: Int -> (Int -> Int) -> Int -> Int\n" +
      "g(x,F) -> F\n" +
      "h :: Int -> Int -> Int\n" +
      "h -> hh\n" +
      "hh :: Int -> Int -> Int\n" +
      "hh(x,y) -> x\n" +
      "main :: (Int -> Int) -> Int -> Int\n" +
      "main(F,x) -> helper(f(x,F))\n" +
      "helper :: (Int -> Int) -> Int\n" +
      "helper(G) -> G(3)\n" +
      "test :: Int\n" +
      "test -> helper2(h, h(0))\n" +
      "helper2 :: (Int -> Int -> Int) -> (Int -> Int) -> Int\n" +
      "helper2(F, G) -> 9\n",
      TrsFactory.LCSTRS);
  }

  private Problem exampleProblem3() {
    Problem prob = (new DPGenerator(exampleTRS3())).queryProblem(true, false);
    return prob.removeDPs(Set.of(0,1,2,4,5), true);
  }


  @Test
  public void testPartialRules() {
    Problem oprob = exampleProblem3();
    MyRedPair mrp = new MyRedPair();
    Processor proc = new URWrtRedPairProcessor(mrp);
    proc.processDPP(oprob);
    assertTrue(mrp._oprob.equals(
      "C) [usable_{f1}]  ==>  f1(x) Weak g1(x) | true {[] }\n" +
      "C) [usable_{f2}]  ==>  f2(x, arg2) Weak g2(x, arg2) | true {[] }\n" +
      "C) [usable_{f3}]  ==>  f3(x, arg2, arg3) Weak g3(x, arg2, arg3) | true {[] }\n" +
      "C) [usable_{g2}]  ==>  g2(x, F) Weak F | true {[] }\n" +
      "C) [usable_{g3}]  ==>  g3(x, F, arg3) Weak $ | true {[] }\n" +
      "C) [usable_{h0}]  ==>  h0 Weak hh0 | true {[] }\n" +
      "C) [usable_{h1}]  ==>  h1(arg1) Weak hh1(arg1) | true {[] }\n" +
      "C) [usable_{h2}]  ==>  h2(arg1, arg2) Weak hh2(arg1, arg2) | true {[] }\n" +
      "C) [usable_{hh2}]  ==>  hh2(x, y) Weak x | true {[] }\n" +
      "C) [usable_{main2}]  ==>  main2(F, x) Weak helper1(f2(x, F)) | true {[] }\n" +
      "C) [usable_{helper1}]  ==>  helper1(G) Weak $ | true {[] }\n" +
      "C) [usable_{test0}]  ==>  test0 Weak helper22(h0, h1(0)) | true {[] }\n" +
      "C) [usable_{helper22}]  ==>  helper22(F, G) Weak 9 | true {[] }\n" +
      "E) 0  :  main#2(F, x) Strict helper#1(f2(x, F)) | true {[] }\n" +
      "E) 1  :  test#0 Strict helper2#2(h0, h1(0)) | true {[] }\n"));
    assertTrue(mrp._smt.equals(
      // regards({f,i) <--> regards{f_n,i} if i ≤ n
      "![regards{f,1}] or [regards{f1,1}]\n" +
      "![regards{f1,1}] or [regards{f,1}]\n" +
      "![regards{f,1}] or [regards{f2,1}]\n" +
      "![regards{f2,1}] or [regards{f,1}]\n" +
      "![regards{f,2}] or [regards{f2,2}]\n" +
      "![regards{f2,2}] or [regards{f,2}]\n" +
      "![regards{f,1}] or [regards{f3,1}]\n" +
      "![regards{f3,1}] or [regards{f,1}]\n" +
      "![regards{f,2}] or [regards{f3,2}]\n" +
      "![regards{f3,2}] or [regards{f,2}]\n" +
      "![regards{f,3}] or [regards{f3,3}]\n" +
      "![regards{f3,3}] or [regards{f,3}]\n" +
      "![regards{g,1}] or [regards{g1,1}]\n" +
      "![regards{g1,1}] or [regards{g,1}]\n" +
      "![regards{g,1}] or [regards{g2,1}]\n" +
      "![regards{g2,1}] or [regards{g,1}]\n" +
      "![regards{g,2}] or [regards{g2,2}]\n" +
      "![regards{g2,2}] or [regards{g,2}]\n" +
      "![regards{g,1}] or [regards{g3,1}]\n" +
      "![regards{g3,1}] or [regards{g,1}]\n" +
      "![regards{g,2}] or [regards{g3,2}]\n" +
      "![regards{g3,2}] or [regards{g,2}]\n" +
      "![regards{g,3}] or [regards{g3,3}]\n" +
      "![regards{g3,3}] or [regards{g,3}]\n" +
      "![regards{helper#,1}] or [regards{helper#1,1}]\n" +
      "![regards{helper#1,1}] or [regards{helper#,1}]\n" +
      "![regards{helper2#,1}] or [regards{helper2#2,1}]\n" +
      "![regards{helper2#2,1}] or [regards{helper2#,1}]\n" +
      "![regards{helper2#,2}] or [regards{helper2#2,2}]\n" +
      "![regards{helper2#2,2}] or [regards{helper2#,2}]\n" +
      "![regards{helper2,1}] or [regards{helper22,1}]\n" +
      "![regards{helper22,1}] or [regards{helper2,1}]\n" +
      "![regards{helper2,2}] or [regards{helper22,2}]\n" +
      "![regards{helper22,2}] or [regards{helper2,2}]\n" +
      "![regards{helper,1}] or [regards{helper1,1}]\n" +
      "![regards{helper1,1}] or [regards{helper,1}]\n" +
      "![regards{hh,1}] or [regards{hh1,1}]\n" +
      "![regards{hh1,1}] or [regards{hh,1}]\n" +
      "![regards{hh,1}] or [regards{hh2,1}]\n" +
      "![regards{hh2,1}] or [regards{hh,1}]\n" +
      "![regards{hh,2}] or [regards{hh2,2}]\n" +
      "![regards{hh2,2}] or [regards{hh,2}]\n" +
      "![regards{h,1}] or [regards{h1,1}]\n" +
      "![regards{h1,1}] or [regards{h,1}]\n" +
      "![regards{h,1}] or [regards{h2,1}]\n" +
      "![regards{h2,1}] or [regards{h,1}]\n" +
      "![regards{h,2}] or [regards{h2,2}]\n" +
      "![regards{h2,2}] or [regards{h,2}]\n" +
      "![regards{main#,1}] or [regards{main#2,1}]\n" +
      "![regards{main#2,1}] or [regards{main#,1}]\n" +
      "![regards{main#,2}] or [regards{main#2,2}]\n" +
      "![regards{main#2,2}] or [regards{main#,2}]\n" +
      "![regards{main,1}] or [regards{main2,1}]\n" +
      "![regards{main2,1}] or [regards{main,1}]\n" +
      "![regards{main,2}] or [regards{main2,2}]\n" +
      "![regards{main2,2}] or [regards{main,2}]\n" +
      // usability requirements
      "![regards{helper#1,1}] or [usable_{f2}]\n" +
      "![regards{helper2#2,1}] or [usable_{h0}]\n" +
      "![regards{helper2#2,2}] or [usable_{h1}]\n" +
      "![usable_{f2}] or [usable_{g2}]\n" +
      "![usable_{f3}] or [usable_{g3}]\n" +
      "![usable_{g3}]\n" +
      "![usable_{h2}] or [usable_{hh2}]\n" +
      "![usable_{main2}] or [usable_{helper1}]\n" +
      "![usable_{main2}] or ![regards{helper1,1}] or [usable_{f2}]\n" +
      "![usable_{helper1}]\n" +
      "![usable_{test0}] or [usable_{helper22}]\n" +
      "![usable_{test0}] or ![regards{helper22,1}] or [usable_{h0}]\n" +
      "![usable_{test0}] or ![regards{helper22,2}] or [usable_{h1}]\n" +
      // extra requirement for higher-order rules
      "![usable_{f2}] or [regards{f,2}] or ![regards{g,2}]\n" +
      "![usable_{f3}] or [regards{f,2}] or ![regards{g,2}]\n" +
      "![usable_{f3}] or [regards{f,3}] or ![regards{g,3}]\n" +
      "![usable_{h1}] or [regards{h,1}] or ![regards{hh,1}]\n" +
      "![usable_{h2}] or [regards{h,1}] or ![regards{hh,1}]\n" +
      "![usable_{h2}] or [regards{h,2}] or ![regards{hh,2}]\n"));
  }
}

