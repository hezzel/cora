/**************************************************************************************************
 Copyright 2024-2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.termination.reduction_pairs.horpo;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.TreeMap;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.smt.*;
import charlie.reader.CoraInputReader;
import cora.io.*;
import cora.termination.reduction_pairs.*;

public class HorpoResultTest {
  private TRS makeTrs(String txt) {
    return CoraInputReader.readTrsFromString(txt);
  }

  @Test
  public void testFailedProof() {
    TRS trs = makeTrs("f :: Int -> Int g :: Int -> Int f(x) -> f(x-1) | x != 0 g(x) -> f(x)");
    SmtProblem smt = new SmtProblem();
    OrderingProblem problem = new OrderingProblem(trs, ArgumentFilter.createEmptyFilter(smt));
    for (Rule r : trs.queryRules()) {
      problem.require(new OrderingRequirement(r, OrderingRequirement.Relation.Strict));
    }
    HorpoResult result = new HorpoResult(problem, "Could not find a proof.");
    assertTrue(result.queryAnswer() == ProofObject.Answer.MAYBE);
    assertFalse(result.isStrictlyOriented(0));
    assertFalse(result.isStrictlyOriented(42));
    OutputModule o = OutputModule.createUnicodeModule(trs);
    result.justify(o);
    assertTrue(o.toString().equals("Could not find a proof.\n\n"));
    FunctionSymbol f = trs.lookupSymbol("f");
    FunctionSymbol g = trs.lookupSymbol("g");
    assertTrue(result.precedence(f, g) == 0);
    assertTrue(result.permutation(f, 3) == 0);
    assertFalse(result.regards(f, 1));
    assertFalse(result.stronglyMonotonic());
  }

  @Test
  public void testStrictProof() {
    TRS trs = makeTrs("f :: Int -> Int g :: Int -> Int h :: Int -> Int -> Int\n" +
                      "j :: Int -> Int -> Int -> Int f(x) -> f(x-1) | x > 0 g(x) -> f(x)");
    SmtProblem smt = new SmtProblem();
    ArgumentFilter filter = new ArgumentFilter(smt);
    OrderingProblem problem = new OrderingProblem(trs, filter);
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      Rule r = trs.queryRule(i);
      problem.requireEither(new OrderingRequirement(r, OrderingRequirement.Relation.Strict), i * 2);
    }
    HorpoParameters param = new HorpoParameters(100,
      new TreeSet<FunctionSymbol>(trs.queryAlphabet().getSymbols()), filter, smt);
    HorpoConstraintList lst = new HorpoConstraintList(new TermPrinter(Set.of()), smt);
    Valuation valuation = new Valuation();
    FunctionSymbol f = trs.lookupSymbol("f");
    FunctionSymbol g = trs.lookupSymbol("g");
    FunctionSymbol h = trs.lookupSymbol("h");
    FunctionSymbol j = trs.lookupSymbol("j");
    valuation.setInt(param.getPrecedence(f).queryIndex(), 1);
    valuation.setInt(param.getPrecedence(g).queryIndex(), 2);
    valuation.setInt(param.getPrecedence(h).queryIndex(), 2);
    valuation.setInt(param.getPrecedence(j).queryIndex(), 1);
    valuation.setInt(param.getPermutation(f, 1).queryIndex(), 1);
    valuation.setInt(param.getPermutation(g, 1).queryIndex(), 1);
    valuation.setInt(param.getPermutation(h, 1).queryIndex(), 2);
    valuation.setInt(param.getPermutation(h, 2).queryIndex(), 1);
    valuation.setInt(param.getPermutation(j, 1).queryIndex(), 1);
    valuation.setInt(param.getPermutation(j, 2).queryIndex(), 3);
    valuation.setInt(param.getPermutation(j, 3).queryIndex(), 1);
    valuation.setBool(filter.regards(f, 1).queryIndex(), true);
    valuation.setBool(filter.regards(g, 1).queryIndex(), true);
    valuation.setBool(filter.regards(h, 1).queryIndex(), true);
    valuation.setBool(filter.regards(h, 2).queryIndex(), true);
    valuation.setBool(filter.regards(j, 1).queryIndex(), true);
    valuation.setBool(filter.regards(j, 2).queryIndex(), true);
    valuation.setBool(filter.regards(j, 3).queryIndex(), true);
    valuation.setBool(param.getDirectionIsDownVariable().queryIndex(), true);

    HorpoResult result = new HorpoResult(problem, Set.of(0), Set.of(), valuation, param, lst);
    assertTrue(result.queryAnswer() == ProofObject.Answer.YES);
    assertTrue(result.isStrictlyOriented(0));
    assertFalse(result.isStrictlyOriented(1));
    assertTrue(result.isStrictlyOriented(0));
    assertFalse(result.isStrictlyOriented(2));
    assertTrue(result.precedence(f, g) == -1);
    assertTrue(result.precedence(f, j) == 0);
    assertTrue(result.precedence(h, g) == 0);
    assertTrue(result.permutation(h, 1) == 2);
    assertTrue(result.permutation(h, 2) == 1);
    assertTrue(result.permutation(j, 2) == 3);
    assertTrue(result.regards(f, 1));
    assertTrue(result.regards(g, 1));
    assertTrue(result.regards(h, 2));
    assertTrue(result.stronglyMonotonic());
    OutputModule o = OutputModule.createUnicodeModule(trs);
    result.justify(o);
    assertTrue(o.toString().equals(
      "Constrained HORPO yields:\n\n" +
      "  f(x) ≻ f(x - 1) | x > 0\n" +
      "  g(x) ≽ f(x)\n\n" +
      "We do this using the following settings:\n\n" +
      "* Monotonicity requirements: this is a strongly monotonic reduction pair " +
        "(all arguments of function symbols were regarded).\n\n" +
      "* Precedence and permutation:\n\n" +
      "    g  { 1 }\n" +
      "  = h  { 2 }   1\n" +
      "  > f  { 1 }\n" +
      "  = j  { 1 3 } _ 2\n\n" +
      "* Well-founded theory orderings:\n\n" +
      "  ⊐_{Bool} = {(true,false)}\n" +
      "  ⊐_{Int}  = {(x,y) | x > -100 ∧ x > y }\n\n"));
  }

  @Test
  public void testNonStrictProof() {
    TRS trs = makeTrs("f :: Int -> Int g :: Int -> Int h :: Int -> Int -> Int\n" +
                      "f(x) -> f(x-1) | x > 0 g(x) -> f(h(x,x))");
    SmtProblem smt = new SmtProblem();
    ArgumentFilter filter = new ArgumentFilter(smt);
    OrderingProblem problem = new OrderingProblem(trs, filter);
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      Rule r = trs.queryRule(i);
      problem.requireEither(new OrderingRequirement(r, OrderingRequirement.Relation.Strict), i * 2);
    }
    HorpoParameters param = new HorpoParameters(3,
      new TreeSet<FunctionSymbol>(trs.queryAlphabet().getSymbols()), filter, smt);
    HorpoConstraintList lst = new HorpoConstraintList(new TermPrinter(Set.of()), smt);
    Valuation valuation = new Valuation();
    FunctionSymbol f = trs.lookupSymbol("f");
    FunctionSymbol g = trs.lookupSymbol("g");
    FunctionSymbol h = trs.lookupSymbol("h");
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    valuation.setInt(param.getPrecedence(f).queryIndex(), 1);
    valuation.setInt(param.getPrecedence(g).queryIndex(), 2);
    valuation.setInt(param.getPrecedence(h).queryIndex(), 2);
    valuation.setBool(filter.regards(f, 1).queryIndex(), true);
    valuation.setBool(filter.regards(g, 1).queryIndex(), false);
    valuation.setBool(filter.regards(h, 1).queryIndex(), false);
    valuation.setBool(filter.regards(h, 2).queryIndex(), true);
    valuation.setInt(param.getPermutation(f, 1).queryIndex(), 1);
    valuation.setInt(param.getPermutation(g, 1).queryIndex(), 0);
    valuation.setInt(param.getPermutation(h, 1).queryIndex(), 0);
    valuation.setInt(param.getPermutation(h, 2).queryIndex(), 2);
    valuation.setBool(param.getDirectionIsDownVariable().queryIndex(), false);
    HorpoResult result = new HorpoResult(problem, Set.of(2), Set.of(), valuation, param, lst);
    assertTrue(result.queryAnswer() == ProofObject.Answer.YES);
    assertFalse(result.isStrictlyOriented(0));
    assertTrue(result.isStrictlyOriented(2));
    assertTrue(result.precedence(f, g) == -1);
    assertTrue(result.precedence(h, g) == 0);
    assertTrue(result.permutation(h, 1) == 0);
    assertTrue(result.permutation(h, 2) == 2);
    assertTrue(result.regards(f, 1));
    assertFalse(result.regards(g, 1));
    assertFalse(result.regards(h, 1));
    assertTrue(result.regards(h, 2));
    assertFalse(result.stronglyMonotonic());
    OutputModule o = OutputModule.createUnicodeModule(trs);
    result.justify(o);
    assertTrue(o.toString().equals(
      "Constrained HORPO yields:\n\n" +
      "  f(x) ≽ f(x - 1) | x > 0\n" +
      "  g(x) ≻ f(h(x, x))\n\n" +
      "We do this using the following settings:\n\n" +
      "* Disregarded arguments:\n\n" +
      "  g 1 \n" +
      "  h 1 \n\n" +
      "* Precedence and permutation:\n\n" +
      "    g  { }\n" +
      "  = h  { }   2\n" +
      "  > f  { 1 }\n\n" +
      "* Well-founded theory orderings:\n\n" +
      "  ⊐_{Bool} = {(true,false)}\n" +
      "  ⊐_{Int}  = {(x,y) | x < 3 ∧ x < y }\n\n"));
  }
}

