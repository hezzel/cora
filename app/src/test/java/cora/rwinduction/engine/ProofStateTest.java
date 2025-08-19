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

import charlie.util.Pair;
import charlie.util.FixedList;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.Term;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.rwinduction.parser.EquationParser;

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
    EquationContext context = EquationParser.parseEquationData("sum1(x) = sum2(x) | x > 0", trs, 1);
    return new ProofState(FixedList.of(context));
  }

  @Test
  public void testToString() {
    TRS trs = setupTRS();
    ProofState state1 = setupProofState(trs);
    Pair<Equation,MutableRenaming> hypo =
      EquationParser.parseEquation("sum1(x) = iter(x, 0, 0) | x > 0", trs);
    ProofState state2 = state1.addHypothesis(new Hypothesis(hypo.fst(), 2, hypo.snd()));
    Rule req = CoraInputReader.readRule("sum1(x) -> iter(x, 0, 0) | x > 0", trs);
    OrdReq r = new OrdReq(req.queryLeftSide(), req.queryRightSide(), req.queryConstraint(),
                          hypo.snd());
    ProofState state3 = state2.addOrderingRequirement(r);
    assertTrue(state1.toString().equals(
      "Equations:\n" +
      " E1: (• , sum1(x) ≈ sum2(x) | x > 0 , •)\n"));
    assertTrue(state2.toString().equals(
      "Equations:\n" +
      " E1: (• , sum1(x) ≈ sum2(x) | x > 0 , •)\n" +
      "Induction hypotheses:\n" +
      " H2: sum1(x) ≈ iter(x, 0, 0) | x > 0\n"));
    assertTrue(state3.toString().equals(
      "Equations:\n" +
      " E1: (• , sum1(x) ≈ sum2(x) | x > 0 , •)\n" +
      "Induction hypotheses:\n" +
      " H2: sum1(x) ≈ iter(x, 0, 0) | x > 0\n" +
      "Ordering requirements:\n" +
      " * sum1(x) ≻ iter(x, 0, 0) | x > 0\n"));
  }

  @Test
  public void testAddReplaceDelete() {
    TRS trs = setupTRS();
    ProofState state1 = setupProofState(trs);
    assertTrue(state1.getLastUsedIndex() == 1);
    EquationContext eq1 = EquationParser.parseEquationData(
      "sum1(x) -><- iter(x, 0, 0) | x > 0", trs, 3);
    EquationContext eq2 =
      EquationParser.parseEquationData("0 -><- iter(x, 0, 0) | x = 0", trs, 4);
    EquationContext eq3 =
      EquationParser.parseEquationData("x + sum1(x-1) -><- iter(x, 0, 0) | x > 0", trs, 7);
    assertTrue(state1.getTopEquation().toString().equals(
      "E1: (• , sum1(x) ≈ sum2(x) | x > 0 , •)"));
    ProofState state2 = state1.replaceTopEquation(eq1);
    assertTrue(state2.getLastUsedIndex() == 3);
    assertTrue(state2.getEquations().size() == 1);
    assertTrue(state2.getTopEquation().toString().equals(
      "E3: (• , sum1(x) ≈ iter(x, 0, 0) | x > 0 , •)"));
    ProofState state3 = state1.addEquation(eq1);
    assertTrue(state3.getLastUsedIndex() == 3);
    assertTrue(state3.getEquations().size() == 2);
    assertTrue(state3.getTopEquation().toString().equals(
      "E3: (• , sum1(x) ≈ iter(x, 0, 0) | x > 0 , •)"));
    assertTrue(state3.getEquations().get(0).toString().equals(
      "E1: (• , sum1(x) ≈ sum2(x) | x > 0 , •)"));
    ProofState state4 = state3.replaceTopEquation(List.of(eq2, eq3));
    assertTrue(state4.getLastUsedIndex() == 7);
    assertTrue(state4.getEquations().size() == 3);
    assertTrue(state4.getTopEquation() == eq3);
    ProofState state5 = state4.deleteTopEquation();
    assertTrue(state5.getEquations().size() == 2);
    assertTrue(state5.getLastUsedIndex() == 7);
    assertTrue(state5.getTopEquation() == eq2);
    ProofState state6 = state5.replaceTopEquation(List.of());
    assertTrue(state6.getEquations().size() == 1);
    assertTrue(state6.getLastUsedIndex() == 7);
    assertTrue(state6.getTopEquation().toString().equals(
      "E1: (• , sum1(x) ≈ sum2(x) | x > 0 , •)"));
    assertFalse(state6.isFinalState());
    ProofState state7 = state6.deleteTopEquation();
    assertTrue(state7.getLastUsedIndex() == 7);
    assertTrue(state7.isFinalState());
    assertThrows(java.lang.IndexOutOfBoundsException.class,
      () -> state7.deleteTopEquation());
    assertThrows(java.lang.IndexOutOfBoundsException.class,
      () -> state7.replaceTopEquation(eq2));
  }

  @Test
  public void testFindHypothesis() {
    TRS trs = setupTRS();
    ProofState state = setupProofState(trs);
    Pair<Equation,MutableRenaming> hypo =
      EquationParser.parseEquation("sum1(x+y) = y * sum1(x)", trs);
    state = state.addHypothesis(new Hypothesis(hypo.fst(), 2, hypo.snd()));
    hypo = EquationParser.parseEquation("sum1(x) = iter(x, 0, 0) | x > 0", trs);
    state = state.addHypothesis(new Hypothesis(hypo.fst(), 17, hypo.snd()));
    assertTrue(state.getHypothesisByName("H2").toString().equals("H2: sum1(x + y) ≈ y * sum1(x)"));
    assertTrue(state.getHypothesisByName("H9") == null);
  }
}

