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
import cora.rwinduction.parser.ExtendedTermParser;

class ProverContextTest {
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

  @Test
  public void testAddUndoRedo() {
    TRS trs = setupTRS();
    Equation eq = ExtendedTermParser.parseEquation("sum1(x) = sum2(x) | x ≥ 0", trs);
    ProverContext context =
      new ProverContext(trs, FixedList.of(eq), new TermPrinter(trs.queryFunctionSymbolNames()));
    ProofState state1 = context.getProofState();
    assertTrue(state1.getEquations().size() == 1);
    assertTrue(state1.getTopEquation() == eq);
    Equation eq2 = ExtendedTermParser.parseEquation("0 -><- iter(x, 0, 0) | x = 0", trs);
    Equation eq3 = ExtendedTermParser.parseEquation("x + sum1(x-1) -><- iter(x, 0, 0) | x > 0", trs);
    ProofState state2 = state1.replaceTopEquation(List.of(eq2, eq3));
    context.addProofStep(state2, "action 1");
    assertTrue(context.getProofState() == state2);
    assertTrue(context.undoProofStep());
    assertTrue(context.getProofState() == state1);
    assertFalse(context.undoProofStep());
    assertTrue(context.getProofState() == state1);
    assertTrue(context.redoProofStep());
    assertTrue(context.getProofState() == state2);
    assertFalse(context.redoProofStep());
    assertTrue(context.getProofState() == state2);
  }

  @Test
  public void testCommandHistory() {
    TRS trs = setupTRS();
    Equation eq = ExtendedTermParser.parseEquation("sum1(x) = sum2(x) | x ≥ 0", trs);
    ProverContext context =
      new ProverContext(trs, FixedList.of(eq), new TermPrinter(trs.queryFunctionSymbolNames()));
    ProofState state1 = context.getProofState();
    assertTrue(state1.getEquations().size() == 1);
    assertTrue(state1.getTopEquation() == eq);
    Equation eq2 = ExtendedTermParser.parseEquation("0 -><- iter(x, 0, 0) | x = 0", trs);
    Equation eq3 = ExtendedTermParser.parseEquation("x + sum1(x-1) -><- iter(x, 0, 0) | x > 0", trs);
    ProofState state2 = state1.replaceTopEquation(List.of(eq2, eq3));
    context.addProofStep(state2, "action 1");
    ProofState state3 = state2.addHypothesis(eq);
    context.addProofStep(state3, "action 2");
    ProofState state4 = state3.deleteTopEquation();
    context.addProofStep(state4, "action 3");
    ProofState state5 = state4.deleteTopEquation();
    context.addProofStep(state5, "action 4");
    assertTrue(context.getProofState().isFinalState());
    List<String> commands = context.getCommandHistory();
    assertTrue(commands.size() == 4);
    assertTrue(commands.get(0).equals("action 1"));
    assertTrue(commands.get(1).equals("action 2"));
    assertTrue(commands.get(2).equals("action 3"));
    assertTrue(commands.get(3).equals("action 4"));
    context.undoProofStep();
    commands = context.getCommandHistory();
    assertTrue(commands.size() == 3);
    assertTrue(commands.get(2).equals("action 3"));
  }
}

