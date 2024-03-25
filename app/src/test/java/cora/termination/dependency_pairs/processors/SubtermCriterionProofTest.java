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

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import java.util.TreeMap;
import java.util.List;
import java.util.Set;

import cora.terms.Term;
import cora.terms.Variable;
import cora.terms.FunctionSymbol;
import cora.trs.TRS;
import cora.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;

class SubtermCriterionProofTest {
  @Test
  public void testNotApplicable() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "f(x,y) -> f(x-y, x+y) | x > y\n");
    Problem start = DPGenerator.generateProblemFromTrs(trs);
    SubtermCriterionProof scp = new SubtermCriterionProof(start);
    assertFalse(scp.applicable());
    assertTrue(scp.queryOutput() == start);
    assertTrue(scp.queryResults() == null);
  }

  @Test
  public void testNothingRemoved() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "g :: Int -> Int -> Int\n" +
      "f(x,y) -> g(y, x-1) | x > y\n" +
      "g(x,y) -> x\n");
    Problem start = DPGenerator.generateProblemFromTrs(trs);
    TreeMap<FunctionSymbol,Integer> projection = new TreeMap<FunctionSymbol,Integer>();
    projection.put(start.getDPList().get(0).lhs().queryRoot(), 2);
    projection.put(start.getDPList().get(0).rhs().queryRoot(), 1);
    SubtermCriterionProof scp = new SubtermCriterionProof(start, Set.of(), projection);
    assertTrue(scp.applicable());
    assertTrue(scp.queryOutput().getDPList().size() == 1);;
    assertTrue(scp.queryResults().size() == 1);
    OutputModule module = DefaultOutputModule.createPlainModule(trs);
    scp.justify(module);
    assertTrue(module.toString().equals(
      "We use the following projection function:\n\n" +
      "  nu(f#) = 2\n" +
      "  nu(g#) = 1\n\n" +
      "We thus have:\n\n" +
      "  (1) y |>=| y\n\n" +
      "We may remove the strictly oriented DPs, which yields:\n\n"));
  }

  @Test
  void testRemovePart() {
    TRS trs = CoraInputReader.readTrsFromString(
      "o :: nat\n" +
      "s :: nat -> nat\n" +
      "ack :: nat -> nat -> nat\n" +
      "ack(o, n) -> s(n)\n" +
      "ack(s(m), o) -> ack(m, s(o))\n" +
      "ack(s(m), s(n)) -> ack(m, ack(s(m), n))\n");
    Problem start = DPGenerator.generateProblemFromTrs(trs);
    TreeMap<FunctionSymbol,Integer> projection = new TreeMap<FunctionSymbol,Integer>();

    FunctionSymbol ack = start.getDPList().get(0).lhs().queryRoot();
    projection.put(ack, 1);
    SubtermCriterionProof scp = new SubtermCriterionProof(start,Set.of(0,2),projection);

    assertTrue(scp.applicable());
    assertTrue(scp.queryInput() == start);
    assertTrue(scp.queryOutput().getDPList().size() == 1);
    assertTrue(scp.queryResults().size() == 1);
    assertTrue(scp.queryProcessorName().equals("Subterm Criterion"));

    OutputModule module = DefaultOutputModule.createUnicodeModule(trs);
    scp.justify(module);
    assertTrue(module.toString().equals(
      "We use the following projection function:\n\n" +
      "  ν(ack#) = 1\n\n" +
      "We thus have:\n\n" +
      "  (1) s(m) ⊳ m\n" +
      "  (2) s(m) ⊵ s(m)\n" +
      "  (3) s(m) ⊳ m\n\n" +
      "We may remove the strictly oriented DPs, which yields:\n\n"));
  }

  @Test
  public void testRemoveAll() {
    TRS trs = CoraInputReader.readTrsFromString(
      "nil :: list\n" +
      "cons :: Int -> list -> list\n" +
      "append :: list -> list -> list\n" +
      "append(cons(x, y), z) -> cons(x, append(y, z))\n");
    Problem start = DPGenerator.generateProblemFromTrs(trs);
    TreeMap<FunctionSymbol,Integer> projection = new TreeMap<FunctionSymbol,Integer>();
    FunctionSymbol append = start.getDPList().get(0).lhs().queryRoot();
    projection.put(append, 1);
    SubtermCriterionProof scp = new SubtermCriterionProof(start,Set.of(0),projection);

    assertTrue(scp.applicable());
    assertTrue(scp.queryInput() == start);
    assertTrue(scp.queryOutput().getDPList().size() == 0);
    assertTrue(scp.queryResults().size() == 0);

    OutputModule module = DefaultOutputModule.createPlainModule(trs);
    scp.justify(module);
    assertTrue(module.toString().equals(
      "We use the following projection function:\n\n" +
      "  nu(append#) = 1\n\n" +
      "We thus have:\n\n" +
      "  (1) cons(x, y) |>| y\n\n" +
      "All DPs are strictly oriented, and may be removed.  Hence, this DP problem is finite.\n\n"));
  }
}
