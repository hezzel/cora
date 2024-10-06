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

package cora.termination.dependency_pairs;

import charlie.exceptions.NullStorageException;
import charlie.types.TypeFactory;
import charlie.terms.*;
import charlie.trs.*;
import charlie.reader.CoraInputReader;

import java.util.Set;
import java.util.List;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class ProblemTest {
  private TRS trs = CoraInputReader.readTrsFromString(
    "mul :: Nat -> Nat -> Nat\n" +
    "add :: Nat -> Nat -> Nat\n" +
    "eval :: Int -> Int -> Int\n" +
    "mul# :: Nat -> Nat -> dpsort\n" +
    "add# :: Nat -> Nat -> dpsort\n" +
    "eval# :: Int -> Int -> dpsort\n" +
    "zero :: Nat\n" +
    "suc :: Nat -> Nat\n" +
    "mul(zero, x) -> x\n" +
    "mul(suc(x), y) -> add(y, mul(x, y))\n" +
    "eval(x, y) -> eval(x - 1, y) | x>y\n");

  private DP createDP1() {
    Renaming renaming = new Renaming(Set.of());
    Term lhs = CoraInputReader.readTerm("eval#(x, y)", renaming, true, trs);
    Term rhs = CoraInputReader.readTerm("eval#(x-1, y)", renaming, true, trs);
    Term constraint = CoraInputReader.readTerm("x > y", renaming, true, trs);
    return new DP(lhs, rhs, constraint);
  }

  private DP createDP2() {
    Renaming renaming = new Renaming(Set.of());
    Term lhs = CoraInputReader.readTerm("add#(suc(x), y)", renaming, true, trs);
    Term rhs = CoraInputReader.readTerm("add#(x, y)", renaming, true, trs);
    return new DP(lhs, rhs);
  }

  private DP createDP3() {
    Renaming renaming = new Renaming(Set.of());
    Term lhs = CoraInputReader.readTerm("mul#(suc(x), y)", renaming, true, trs);
    Term rhs = CoraInputReader.readTerm("add#(x, mul(x, y))", renaming, true, trs);
    return new DP(lhs, rhs);
  }

  @Test
  void testCreateProblem() {
    List<DP> dps = List.of(createDP1(), createDP2(), createDP3());
    List<Rule> rules = trs.queryRules();
    Set<Integer> priv = Set.of(1);
    Problem problem = new Problem(dps, rules, priv, trs, false, true,
                                  Problem.TerminationFlag.Computable);
    assertTrue(problem.getDPList() == dps);
    assertTrue(problem.getRuleList() == rules);
    assertTrue(problem.hasExtraRules());
    assertFalse(problem.isInnermost());
    assertTrue(problem.hasPrivateDPs());
    assertTrue(problem.isPrivate(1));
    assertFalse(problem.isPrivate(2));
    assertTrue(problem.queryTerminationStatus() == Problem.TerminationFlag.Computable);
    assertTrue(problem.terminating());
    assertFalse(problem.isEmpty());
    assertTrue(problem.toString().equals(
      "DPs:\n" +
      "  eval#(x, y) => eval#(x - 1, y) | x > y { }\n" +
      "  add#(suc(x), y) => add#(x, y) | true { } (private)\n" +
      "  mul#(suc(x), y) => add#(x, mul(x, y)) | true { }\n" +
      "Rules:\n" +
      "  mul(zero, x) → x\n" +
      "  mul(suc(x), y) → add(y, mul(x, y))\n" +
      "  eval(x, y) → eval(x - 1, y) | x > y\n" +
      "  ... and an unknown number of additional rules\n" +
      "Evaluation is arbitrary.\n" +
      "Right-hand sides are expected to be Computable.\n"
    ));
  }

  @Test
  public void testProblemWithNullPrivates() {
    List<DP> dps = List.of(createDP1(), createDP2(), createDP3());
    List<Rule> rules = trs.queryRules();
    Problem problem = new Problem(dps, rules, null, trs, true, false,
                                  Problem.TerminationFlag.Arbitrary);
    assertFalse(problem.hasExtraRules());
    assertTrue(problem.isInnermost());
    assertFalse(problem.hasPrivateDPs());
    assertFalse(problem.isPrivate(1));
    assertTrue(problem.queryTerminationStatus() == Problem.TerminationFlag.Arbitrary);
    assertFalse(problem.terminating());
    assertFalse(problem.isEmpty());
  }

  @Test
  public void testHeads() {
    List<DP> dps = List.of(createDP1(), createDP2(), createDP2());
    List<Rule> rules = trs.queryRules();
    Set<Integer> priv = Set.of();
    Problem problem = new Problem(dps, rules, priv, trs, false, true,
                                  Problem.TerminationFlag.Computable);
    assertFalse(problem.hasPrivateDPs());
    Set<FunctionSymbol> sharpheads = problem.getHeads();
    assertTrue(sharpheads.size() == 2);
    assertTrue(sharpheads.toString().equals("[add#, eval#]"));
  }

  @Test
  public void testHeadsNonRec() {
    List<DP> dps = List.of(createDP3());
    List<Rule> rules = trs.queryRules();
    Set<Integer> priv = Set.of();
    Problem problem = new Problem(dps, rules, priv, trs, false, true,
      Problem.TerminationFlag.Computable);
    assertFalse(problem.hasPrivateDPs());
    Set<FunctionSymbol> sharpheads = problem.getHeads();
    assertEquals(2, sharpheads.size());
    assertEquals("[add#, mul#]", sharpheads.toString());
  }

  @Test
  public void testNullCreation() {
    List<DP> dps = List.of(createDP1(), createDP2(), createDP2());
    List<Rule> rules = trs.queryRules();
    Set<Integer> priv = Set.of();
    assertThrows(NullStorageException.class, () ->
      new Problem(null, rules, priv, trs, false, true, Problem.TerminationFlag.Terminating));
    assertThrows(NullStorageException.class, () ->
      new Problem(dps, null, priv, trs, false, true, Problem.TerminationFlag.Terminating));
    assertThrows(NullStorageException.class, () ->
      new Problem(dps, rules, priv, null, true, false, Problem.TerminationFlag.Terminating));
  }

  @Test
  void testRemove() {
    // set up problem
    DP dp0 = createDP1();
    DP dp1 = createDP2();
    DP dp2 = createDP3();
    DP dp3 = createDP1();
    List<DP> dps = List.of(dp0, dp1, dp2, dp3);
    List<Rule> rules = trs.queryRules();
    Set<Integer> priv = Set.of(0, 2);
    Problem problem = new Problem(dps, rules, priv, trs, false, true,
                                  Problem.TerminationFlag.Computable);

    // remove DP 0; DP 2 (now DP 1) remains private
    Problem prob = problem.removeDPs(Set.of(0), false);
    assertTrue(problem.getDPList().size() == 4);
    assertTrue(prob.getDPList().size() == 3);
    assertTrue(prob.getDPList().get(0) == problem.getDPList().get(1));
    assertTrue(prob.getDPList().get(1) == problem.getDPList().get(2));
    assertTrue(prob.getDPList().get(2) == problem.getDPList().get(3));
    assertTrue(prob.hasPrivateDPs());
    assertFalse(prob.isPrivate(0));
    assertTrue(prob.isPrivate(1));
    assertFalse(prob.isPrivate(2));

    // remove dp1 and dp3 from the original problem, and this time do remove privateness
    prob = problem.removeDPs(Set.of(1, 3), true);
    assertTrue(problem.getDPList().size() == 4);
    assertTrue(prob.getDPList().size() == 2);
    assertTrue(prob.getDPList().get(0) == problem.getDPList().get(0));
    assertTrue(prob.getDPList().get(1) == problem.getDPList().get(2));
    assertFalse(prob.hasPrivateDPs());
    assertFalse(prob.isPrivate(0));
    assertFalse(prob.isPrivate(1));

    // remove a DP that's not there -- this doesn't do anything
    Problem prob2 = prob.removeDPs(Set.of(3), false);
    assertTrue(prob2.getDPList().size() == 2);

    // remove the remaining DPs
    assertTrue(prob.removeDPs(Set.of(0, 1), true).isEmpty());
  }
}

