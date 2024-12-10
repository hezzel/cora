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
import charlie.terms.Renaming;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.rwinduction.parser.ExtendedTermParser;

class ProofStateTest {
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

  private ProofState setupProofState(TRS trs) {
    Equation equation = ExtendedTermParser.parseEquation("sum1(x) = sum2(x) | x > 0", trs);
    return new ProofState(FixedList.of(equation));
  }

  @Test
  public void testToString() {
    TRS trs = setupTRS();
    ProofState state1 = setupProofState(trs);
    Equation hypo = ExtendedTermParser.parseEquation("sum1(x) = iter(x, 0, 0) | x > 0", trs);
    ProofState state2 = state1.addHypothesis(hypo);
    Rule req = CoraInputReader.readRule("sum1(x) -> iter(x, 0, 0) | x > 0", trs);
    ProofState state3 = state2.addOrderingRequirement(req);
    assertTrue(state1.toString().equals(
      "Equations:\n" +
      " * sum1(x) ≈ sum2(x) | x > 0\n"));
    assertTrue(state2.toString().equals(
      "Equations:\n" +
      " * sum1(x) ≈ sum2(x) | x > 0\n" +
      "Induction hypotheses:\n" +
      " * sum1(x) ≈ iter(x, 0, 0) | x > 0\n"));
    assertTrue(state3.toString().equals(
      "Equations:\n" +
      " * sum1(x) ≈ sum2(x) | x > 0\n" +
      "Induction hypotheses:\n" +
      " * sum1(x) ≈ iter(x, 0, 0) | x > 0\n" +
      "Ordering requirements: all rules and\n" +
      " * sum1(x) → iter(x, 0, 0) | x > 0\n"));
  }

  @Test
  public void testAddReplaceDelete() {
    TRS trs = setupTRS();
    ProofState state1 = setupProofState(trs);
    Equation eq1 = ExtendedTermParser.parseEquation("sum1(x) -><- iter(x, 0, 0) | x > 0", trs);
    Equation eq2 = ExtendedTermParser.parseEquation("0 -><- iter(x, 0, 0) | x = 0", trs);
    Equation eq3 = ExtendedTermParser.parseEquation("x + sum1(x-1) -><- iter(x, 0, 0) | x > 0", trs);
    assertTrue(state1.getTopEquation().toString().equals("sum1(x) ≈ sum2(x) | x > 0"));
    ProofState state2 = state1.replaceTopEquation(eq1);
    assertTrue(state2.getEquations().size() == 1);
    assertTrue(state2.getTopEquation().toString().equals("sum1(x) ≈ iter(x, 0, 0) | x > 0"));
    ProofState state3 = state1.addEquation(eq1);
    assertTrue(state3.getEquations().size() == 2);
    assertTrue(state3.getTopEquation().toString().equals("sum1(x) ≈ iter(x, 0, 0) | x > 0"));
    assertTrue(state3.getEquations().get(0).toString().equals("sum1(x) ≈ sum2(x) | x > 0"));
    ProofState state4 = state3.replaceTopEquation(List.of(eq2, eq3));
    assertTrue(state4.getEquations().size() == 3);
    assertTrue(state4.getTopEquation() == eq3);
    ProofState state5 = state4.deleteTopEquation();
    assertTrue(state5.getEquations().size() == 2);
    assertTrue(state5.getTopEquation() == eq2);
    ProofState state6 = state5.replaceTopEquation(List.of());
    assertTrue(state6.getEquations().size() == 1);
    assertTrue(state6.getTopEquation().toString().equals("sum1(x) ≈ sum2(x) | x > 0"));
    assertFalse(state6.isFinalState());
    ProofState state7 = state6.deleteTopEquation();
    assertTrue(state7.isFinalState());
    assertThrows(charlie.exceptions.IndexingException.class,
      () -> state7.deleteTopEquation());
    assertThrows(charlie.exceptions.IndexingException.class,
      () -> state7.replaceTopEquation(eq2));
  }
}

