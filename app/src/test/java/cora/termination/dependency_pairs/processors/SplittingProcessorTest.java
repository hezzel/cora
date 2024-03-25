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

import cora.reader.CoraInputReader;
import cora.trs.TRS;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.DP;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class SplittingProcessorTest {
  @Test
  void testNothingToSplit() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "f(x, y) -> f(x, y-1) | x < y ∧ (1 = 2 ∧ x < y + 1)"
    );

    Problem p = DPGenerator.generateProblemFromTrs(trs);
    SplittingProcessor splitProc = new SplittingProcessor();
    assertFalse(splitProc.processDPP(p).applicable());
  }

  @Test
  public void testObviousSplitNeq() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "f(x ,y) -> f(x, y-1) | x != y");
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    SplittingProcessor splitProc = new SplittingProcessor();
    ProcessorProofObject result = splitProc.processDPP(p);
    assertTrue(result.applicable());
    assertTrue(result.queryResults().size() == 1);
    assertTrue(result.queryResults().get(0).toString().equals(
      "  f#(x, y) -> f#(x, y - 1) [ x > y ] \n" +
      "  f#(x, y) -> f#(x, y - 1) [ x < y ] \n"));
  }

  @Test
  public void testObviousSplitOr() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "f(x ,y) -> f(x, y-1) | x = 1 ∨ x = 3 ∨ x = 10");
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    SplittingProcessor splitProc = new SplittingProcessor();
    ProcessorProofObject result = splitProc.processDPP(p);
    assertTrue(result.applicable());
    assertTrue(result.queryResults().size() == 1);
    assertTrue(result.queryResults().get(0).toString().equals(
      "  f#(x, y) -> f#(x, y - 1) [ x = 1 ] \n" +
      "  f#(x, y) -> f#(x, y - 1) [ x = 3 ] \n" +
      "  f#(x, y) -> f#(x, y - 1) [ x = 10 ] \n"));
  }

  @Test
  public void testNeqAtStartOfConstraint() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "f(x, y) -> f(x, y-1) | x != y ∧ x ≤ y");
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    SplittingProcessor splitProc = new SplittingProcessor();
    ProcessorProofObject result = splitProc.processDPP(p);
    assertTrue(result.applicable());
    assertTrue(result.queryResults().size() == 1);
    assertTrue(result.queryResults().get(0).toString().equals(
      "  f#(x, y) -> f#(x, y - 1) [ x > y ∧ x ≤ y ] \n" +
      "  f#(x, y) -> f#(x, y - 1) [ x < y ∧ x ≤ y ] \n"));
  }

  @Test
  public void testOrInMiddleOfConstraint() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int\n" +
      "g :: Int -> Int\n" +
      "h :: Int -> Int\n" +
      "f(x) -> f(x+1) | 3 = 4 ∧ (x < 0 ∨ x > 10)" +
      "g(x) -> f(x) | x <= 0");
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    SplittingProcessor splitProc = new SplittingProcessor();
    ProcessorProofObject result = splitProc.processDPP(p);
    assertTrue(result.applicable());
    assertTrue(result.queryResults().size() == 1);
    assertTrue(result.queryResults().get(0).toString().equals(
      "  f#(x) -> f#(x + 1) [ 3 = 4 ∧ x < 0 ] \n" +
      "  f#(x) -> f#(x + 1) [ 3 = 4 ∧ x > 10 ] \n" +
      "  g#(x) -> f#(x) [ x ≤ 0 ] \n"));
  }

  @Test
  public void testTwoSplittables() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "f(x,y) -> f(x+2,y-1) | x != y ∧ y > 0 ∧ (x % 2 = 0 ∨ x % 3 != 0)");
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    SplittingProcessor splitProc = new SplittingProcessor();
    ProcessorProofObject result = splitProc.processDPP(p);
    assertTrue(result.applicable());
    assertTrue(result.queryResults().size() == 1);
    List<DP> lst = result.queryResults().get(0).getDPList();
    assertTrue(lst.size() == 4);
    assertTrue(lst.get(0).constraint().toString().equals("x > y ∧ y > 0 ∧ x % 2 = 0"));
    assertTrue(lst.get(1).constraint().toString().equals("x < y ∧ y > 0 ∧ x % 2 = 0"));
    assertTrue(lst.get(2).constraint().toString().equals("x > y ∧ y > 0 ∧ x % 3 ≠ 0"));
    assertTrue(lst.get(3).constraint().toString().equals("x < y ∧ y > 0 ∧ x % 3 ≠ 0"));
  }

  @Test
  public void testTripleSplittables() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "f(x,y) -> f(x+2,y-1) | x != y ∧ y != 0 ∧ (x % 2 = 0 ∨ x % 3 != 0)");
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    SplittingProcessor splitProc = new SplittingProcessor();
    assertFalse(splitProc.processDPP(p).applicable());
  }
}
