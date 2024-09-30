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

import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.FunctionSymbol;
import charlie.terms.TermFactory;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;

class IntegerMappingProofTest {
  @Test
  void testRemoveEverything() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> o\n" +
      "g :: Int -> Int -> o\n" +
      "f(x, y) -> g(x-1, y)   | x > 0 ∧ y > 0\n" +
      "g(x, y) -> f(x, y-1)   | x > 0 ∧ y > 0\n");
    Problem start = (new DPGenerator(trs)).queryProblem(false, true);
    TreeMap<FunctionSymbol,Term> interpretation = new TreeMap<FunctionSymbol,Term>();
    TreeMap<FunctionSymbol,List<Variable>> varlist = new TreeMap<FunctionSymbol,List<Variable>>();

    FunctionSymbol f = start.getDPList().get(0).lhs().queryRoot();
    Term fintp = CoraInputReader.readTerm("arg1 + arg2", trs);
    Variable x = fintp.queryArgument(1).queryVariable();
    Variable y = fintp.queryArgument(2).queryVariable();
    interpretation.put(f, fintp);
    varlist.put(f, List.of(x, y));

    FunctionSymbol g = start.getDPList().get(1).lhs().queryRoot();
    Term gintp = CoraInputReader.readTerm("2 * arg1 + arg2", trs);
    x = gintp.queryArgument(1).queryArgument(2).queryVariable();
    y = gintp.queryArgument(2).queryVariable();
    interpretation.put(g, gintp);
    varlist.put(g, List.of(x, y));

    IntegerMappingProof ifp = new IntegerMappingProof(start,Set.of(0,1),varlist,interpretation);
    
    assertTrue(ifp.applicable());
    assertTrue(ifp.queryInput() == start);
    assertTrue(ifp.queryOutput().getDPList().size() == 0);
    assertTrue(ifp.queryResults().size() == 0);
    assertTrue(ifp.queryProcessorName().equals("Integer Function"));

    OutputModule module = DefaultOutputModule.createPlainModule(trs);
    ifp.justify(module);
    assertTrue(module.toString().equals(
      "We use the following integer mapping:\n\n" +
      "  J(f#) = arg1 + arg2\n" +
      "  J(g#) = 2 * arg1 + arg2\n\n" +
      "We thus have:\n\n" +
      "  (1) x > 0 /\\ y > 0 |= x + y     > 2 * (x - 1) + y (and x + y >= 0)\n" +
      "  (2) x > 0 /\\ y > 0 |= 2 * x + y > x + (y - 1)     (and 2 * x + y >= 0)\n\n" +
      "All DPs are strictly oriented, and may be removed.  Hence, this DP problem is finite.\n\n"));
  }

  @Test
  public void testRemoveJustOne() {
    TRS trs = CoraInputReader.readTrsFromString(
      "private f :: Int -> Int -> o\n" +
      "private g :: Int -> Int -> o\n" +
      "f(x, y) -> g(x-1, y) | x > 0 ∧ y > 0\n" +
      "g(x, y) -> f(x, y-1) | x > 0 ∧ y > 0\n");
    Problem start = (new DPGenerator(trs)).queryProblem(true, false);
    TreeMap<FunctionSymbol,Term> interpretation = new TreeMap<FunctionSymbol,Term>();
    TreeMap<FunctionSymbol,List<Variable>> varlist = new TreeMap<FunctionSymbol,List<Variable>>();

    FunctionSymbol f = start.getDPList().get(0).lhs().queryRoot();
    Variable x = TermFactory.createVar("arg1", CoraInputReader.readType("Int"));
    Variable y = TermFactory.createVar("arg2", CoraInputReader.readType("Int"));
    interpretation.put(f, x);
    varlist.put(f, List.of(x, y));

    FunctionSymbol g = start.getDPList().get(1).lhs().queryRoot();
    interpretation.put(g, x);
    varlist.put(g, List.of(x, y));

    IntegerMappingProof ifp = new IntegerMappingProof(start,Set.of(0),varlist,interpretation);
    
    assertTrue(ifp.applicable());
    assertTrue(ifp.queryInput() == start);
    assertTrue(ifp.queryOutput().getDPList().size() == 1);
    assertTrue(ifp.queryResults().size() == 1);
    assertTrue(ifp.queryProcessorName().equals("Integer Function"));
    assertFalse(ifp.queryResults().get(0).hasPrivateDPs());
    assertFalse(ifp.queryResults().get(0).hasExtraRules());
    assertTrue(ifp.queryResults().get(0).isInnermost());

    OutputModule module = DefaultOutputModule.createUnicodeModule(trs);
    ifp.justify(module);
    assertTrue(module.toString().equals(
      "We use the following integer mapping:\n\n" +
      "  J(f#) = arg1\n" +
      "  J(g#) = arg1\n\n" +
      "We thus have:\n\n" +
      "  (1) x > 0 ∧ y > 0 ⊨ x > x - 1 (and x ≥ 0)\n" +
      "  (2) x > 0 ∧ y > 0 ⊨ x ≥ x\n\n" +
      "We may remove the strictly oriented DPs, which yields:\n\n"));
  }
}
