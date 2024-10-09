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
      "(not [regards{leq,1}]) or [regards{leq1,1}]\n" +
      "(not [regards{leq1,1}]) or [regards{leq,1}]\n" +
      "(not [regards{leq,1}]) or [regards{leq2,1}]\n" +
      "(not [regards{leq2,1}]) or [regards{leq,1}]\n" +
      "(not [regards{leq,2}]) or [regards{leq2,2}]\n" +
      "(not [regards{leq2,2}]) or [regards{leq,2}]\n" +
      "(not [regards{min,1}]) or [regards{min2,1}]\n" +
      "(not [regards{min2,1}]) or [regards{min,1}]\n" +
      "(not [regards{min,2}]) or [regards{min2,2}]\n" +
      "(not [regards{min2,2}]) or [regards{min,2}]\n" +
      "(not [regards{quot,1}]) or [regards{quot2,1}]\n" +
      "(not [regards{quot2,1}]) or [regards{quot,1}]\n" +
      "(not [regards{quot,2}]) or [regards{quot2,2}]\n" +
      "(not [regards{quot2,2}]) or [regards{quot,2}]\n" +
      "(not [regards{sma#,1}]) or [regards{sma#3,1}]\n" +
      "(not [regards{sma#3,1}]) or [regards{sma#,1}]\n" +
      "(not [regards{sma#,2}]) or [regards{sma#3,2}]\n" +
      "(not [regards{sma#3,2}]) or [regards{sma#,2}]\n" +
      "(not [regards{sma#,3}]) or [regards{sma#3,3}]\n" +
      "(not [regards{sma#3,3}]) or [regards{sma#,3}]\n" +
      "(not [regards{sma,1}]) or [regards{sma3,1}]\n" +
      "(not [regards{sma3,1}]) or [regards{sma,1}]\n" +
      "(not [regards{sma,2}]) or [regards{sma3,2}]\n" +
      "(not [regards{sma3,2}]) or [regards{sma,2}]\n" +
      "(not [regards{sma,3}]) or [regards{sma3,3}]\n" +
      "(not [regards{sma3,3}]) or [regards{sma,3}]\n" +
      "(not [regards{start#,1}]) or [regards{start#2,1}]\n" +
      "(not [regards{start#2,1}]) or [regards{start#,1}]\n" +
      "(not [regards{start#,2}]) or [regards{start#2,2}]\n" +
      "(not [regards{start#2,2}]) or [regards{start#,2}]\n" +
      "(not [regards{start,1}]) or [regards{start2,1}]\n" +
      "(not [regards{start2,1}]) or [regards{start,1}]\n" +
      "(not [regards{start,2}]) or [regards{start2,2}]\n" +
      "(not [regards{start2,2}]) or [regards{start,2}]\n" +
      "(not [regards{s,1}]) or [regards{s1,1}]\n" +
      "(not [regards{s1,1}]) or [regards{s,1}]\n" +
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
      "skip(k, cons(x, ys)) -> skip(k-1, ys) | k > 0\n" +
      "skipfold :: (A -> B -> B) -> B -> Int -> list -> B\n" +
      "skipfold(F, n, k, nil) -> n\n" +
      "skipfold(F, n, k, cons(x, ys)) -> skipfold(F, F(x, n), k, skip(k, ys))\n" +
      "zip :: list -> list -> list\n" +
      "zip(nil, ys) -> ys\n" +
      "zip(cons(x, xs), ys) -> cons(x, zip(ys, xs))\n",
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
      "C) [usable_{skip2}]  ==>  skip2(k, cons2(x, ys)) Weak skip2(k - 1, ys) | k > 0 {[k] }\n" +
      "C) [usable_{skipfold4}]  ==>  skipfold4(F, n, k, nil0) Weak n | true {[] }\n" +
      "C) [usable_{skipfold4}]  ==>  skipfold4(F, n, k, cons2(x, ys)) Weak skipfold4(F, $, k, skip2(k, ys)) | true {[] }\n" +
      "C) [usable_{zip2}]  ==>  zip2(nil0, ys) Weak ys | true {[] }\n" +
      "C) [usable_{zip2}]  ==>  zip2(cons2(x, xs), ys) Weak cons2(x, zip2(ys, xs)) | true {[] }\n" +
      "E) 0  :  skipfold#4(F, n, k, cons2(x, ys)) Strict skipfold#4(F, $, k, skip2(k, ys)) | true {[] }\n"));
    assertTrue(mrp._smt.toString().equals(
      "(not [regards{cons,1}]) or [regards{cons2,1}]\n" +
      "(not [regards{cons2,1}]) or [regards{cons,1}]\n" +
      "(not [regards{cons,2}]) or [regards{cons2,2}]\n" +
      "(not [regards{cons2,2}]) or [regards{cons,2}]\n" +
      "(not [regards{skipfold#,1}]) or [regards{skipfold#4,1}]\n" +
      "(not [regards{skipfold#4,1}]) or [regards{skipfold#,1}]\n" +
      "(not [regards{skipfold#,2}]) or [regards{skipfold#4,2}]\n" +
      "(not [regards{skipfold#4,2}]) or [regards{skipfold#,2}]\n" +
      "(not [regards{skipfold#,3}]) or [regards{skipfold#4,3}]\n" +
      "(not [regards{skipfold#4,3}]) or [regards{skipfold#,3}]\n" +
      "(not [regards{skipfold#,4}]) or [regards{skipfold#4,4}]\n" +
      "(not [regards{skipfold#4,4}]) or [regards{skipfold#,4}]\n" +
      "(not [regards{skipfold,1}]) or [regards{skipfold4,1}]\n" +
      "(not [regards{skipfold4,1}]) or [regards{skipfold,1}]\n" +
      "(not [regards{skipfold,2}]) or [regards{skipfold4,2}]\n" +
      "(not [regards{skipfold4,2}]) or [regards{skipfold,2}]\n" +
      "(not [regards{skipfold,3}]) or [regards{skipfold4,3}]\n" +
      "(not [regards{skipfold4,3}]) or [regards{skipfold,3}]\n" +
      "(not [regards{skipfold,4}]) or [regards{skipfold4,4}]\n" +
      "(not [regards{skipfold4,4}]) or [regards{skipfold,4}]\n" +
      "(not [regards{skip,1}]) or [regards{skip2,1}]\n" +
      "(not [regards{skip2,1}]) or [regards{skip,1}]\n" +
      "(not [regards{skip,2}]) or [regards{skip2,2}]\n" +
      "(not [regards{skip2,2}]) or [regards{skip,2}]\n" +
      "(not [regards{zip,1}]) or [regards{zip2,1}]\n" +
      "(not [regards{zip2,1}]) or [regards{zip,1}]\n" +
      "(not [regards{zip,2}]) or [regards{zip2,2}]\n" +
      "(not [regards{zip2,2}]) or [regards{zip,2}]\n" +
      "![regards{skipfold#4,2}]\n" +
      "![regards{skipfold#4,4}] or [usable_{skip2}]\n" +
      "![usable_{skipfold4}] or ![regards{skipfold4,2}]\n" +
      "![usable_{skipfold4}] or ![regards{skipfold4,4}] or [usable_{skip2}]\n"));
  }

  @Test
  public void testExtraRequirement() {
    // TODO
  }
}

