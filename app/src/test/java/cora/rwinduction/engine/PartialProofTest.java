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

package cora.rwinduction.engine;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;
import java.util.Set;

import charlie.util.FixedList;
import charlie.terms.Term;
import charlie.terms.TermPrinter;
import charlie.terms.Renaming;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.io.ParseableTermPrinter;
import cora.rwinduction.parser.ExtendedTermParser;

class PartialProofTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "sum1 :: Int -> Int\n" +
      "sum1(x) -> 0 | x <= 0\n" +
      "sum1(x) -> x + sum1(x-1) | x > 0\n" +
      "sum2 :: Int -> Int\n" +
      "sum2(x) -> iter(x, 0, 0)\n" +
      "iter :: Int -> Int -> Int -> Int\n" +
      "iter(x, i, z) -> z | i > x\n" +
      "iter(x, i, z) -> iter(x, i+1, z+i) | i <= x\n");
  }

  private class MyStep extends DeductionStep {
    private String _txt;
    public MyStep(String txt) { _txt = txt; }
    protected ProofState applyIgnoreExceptions(PartialProof proof) { return null; }
    public String commandDescription(ParseableTermPrinter termPrinter) { return _txt; }
    public void explain(OutputModule module) { module.println("Explanation: %a", _txt); }
  }

  @Test
  public void testAddUndoRedo() {
    TRS trs = setupTRS();
    Equation eq = ExtendedTermParser.parseEquation("sum1(x) = sum2(x) | x ≥ 0", trs, 11);
    PartialProof proof =
      new PartialProof(trs, FixedList.of(eq), new TermPrinter(trs.queryFunctionSymbolNames()));
    ProofState state1 = proof.getProofState();
    assertTrue(state1.getEquations().size() == 1);
    assertTrue(state1.getTopEquation() == eq);
    assertTrue(proof.getFirstAvailableIndex() == 12);
    Equation eq2 = ExtendedTermParser.parseEquation("0 -><- iter(x, 0, 0) | x = 0", trs, 19);
    Equation eq3 =
      ExtendedTermParser.parseEquation("x + sum1(x-1) -><- iter(x, 0, 0) | x > 0", trs, 18);
    assertTrue(proof.getFirstAvailableIndex() == 12);
    ProofState state2 = state1.replaceTopEquation(List.of(eq2, eq3));
    proof.addProofStep(state2, new MyStep("action 1"));
    assertTrue(proof.getFirstAvailableIndex() == 20);
    assertTrue(proof.getProofState() == state2);
    proof.addProofStep(state1, new MyStep("double delete"));
    assertTrue(proof.getProofState() == state1);
    assertTrue(proof.getFirstAvailableIndex() == 20);
    assertTrue(proof.undoProofStep());
    assertTrue(proof.getProofState() == state2);
    assertTrue(proof.undoProofStep());
    assertTrue(proof.getProofState() == state1);
    assertTrue(proof.getFirstAvailableIndex() == 12);
    assertFalse(proof.undoProofStep());
    assertTrue(proof.getProofState() == state1);
    assertTrue(proof.getFirstAvailableIndex() == 12);
    assertTrue(proof.redoProofStep());
    assertTrue(proof.getProofState() == state2);
    assertTrue(proof.getFirstAvailableIndex() == 20);
    assertTrue(proof.redoProofStep());
    assertTrue(proof.getProofState() == state1);
    assertFalse(proof.redoProofStep());
    assertTrue(proof.getProofState() == state1);
    assertTrue(proof.getFirstAvailableIndex() == 20);
  }

  @Test
  public void testCommandHistory() {
    TRS trs = setupTRS();
    Equation eq = ExtendedTermParser.parseEquation("sum1(x) = sum2(x) | x ≥ 0", trs, 3);
    PartialProof proof =
      new PartialProof(trs, FixedList.of(eq), new TermPrinter(trs.queryFunctionSymbolNames()));
    ProofState state1 = proof.getProofState();
    assertTrue(state1.getEquations().size() == 1);
    assertTrue(state1.getTopEquation() == eq);
    Equation eq2 = ExtendedTermParser.parseEquation("0 -><- iter(x, 0, 0) | x = 0", trs, 4);
    Equation eq3 = ExtendedTermParser.parseEquation("x + sum1(x-1) = iter(x,0,0) | x > 0", trs, 5);
    ProofState state2 = state1.replaceTopEquation(List.of(eq2, eq3));
    proof.addProofStep(state2, new MyStep("action 1"));
    ProofState state3 = state2.addHypothesis(eq);
    proof.addProofStep(state3, new MyStep("action 2"));
    ProofState state4 = state3.deleteTopEquation();
    proof.addProofStep(state4, new MyStep("action 3"));
    ProofState state5 = state4.deleteTopEquation();
    proof.addProofStep(state5, new MyStep("action 4"));
    assertTrue(proof.getProofState().isFinalState());
    List<String> commands = proof.getCommandHistory();
    assertTrue(commands.size() == 4);
    assertTrue(commands.get(0).equals("action 1"));
    assertTrue(commands.get(1).equals("action 2"));
    assertTrue(commands.get(2).equals("action 3"));
    assertTrue(commands.get(3).equals("action 4"));
    proof.undoProofStep();
    commands = proof.getCommandHistory();
    assertTrue(commands.size() == 3);
    assertTrue(commands.get(2).equals("action 3"));
  }
}

