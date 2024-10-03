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

package cora.termination.reduction_pairs.horpo;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;
import java.util.Set;
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
    OrderingProblem problem = new OrderingProblem(trs, new StrongMonotonicity(smt));
    for (Rule r : trs.queryRules()) {
      problem.require(new OrderingRequirement(r, OrderingRequirement.Relation.Strict));
    }
    HorpoResult result = new HorpoResult(problem, "Could not find a proof.");
    assertTrue(result.queryAnswer() == ProofObject.Answer.MAYBE);
    assertFalse(result.isStrictlyOriented(0));
    assertFalse(result.isStrictlyOriented(42));
    OutputModule o = DefaultOutputModule.createUnicodeModule(trs);
    result.justify(o);
    assertTrue(o.toString().equals("Could not find a proof.\n\n"));
    FunctionSymbol f = trs.lookupSymbol("f");
    FunctionSymbol g = trs.lookupSymbol("g");
    assertTrue(result.precedence(f, g) == 0);
    assertTrue(result.status(f) == null);
    assertFalse(result.regards(f, 1));
    assertFalse(result.stronglyMonotonic());
  }

  @Test
  public void testStrictProof() {
    TRS trs = makeTrs("f :: Int -> Int g :: Int -> Int h :: Int -> Int -> Int\n" +
                      "j :: Int -> Int -> Int f(x) -> f(x-1) | x > 0 g(x) -> f(x)");
    SmtProblem smt = new SmtProblem();
    Monotonicity mono = new StrongMonotonicity(smt);
    OrderingProblem problem = new OrderingProblem(trs, mono);
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      Rule r = trs.queryRule(i);
      problem.requireEither(new OrderingRequirement(r, OrderingRequirement.Relation.Strict), i * 2);
    }
    HorpoParameters param = new HorpoParameters(100, smt);
    HorpoConstraintList lst = new HorpoConstraintList(new TermPrinter(Set.of()), smt);
    Valuation valuation = new Valuation();
    FunctionSymbol f = trs.lookupSymbol("f");
    FunctionSymbol g = trs.lookupSymbol("g");
    FunctionSymbol h = trs.lookupSymbol("h");
    FunctionSymbol j = trs.lookupSymbol("j");
    valuation.setInt(param.getPrecedenceFor(f).queryIndex(), 1);
    valuation.setInt(param.getPrecedenceFor(g).queryIndex(), 2);
    valuation.setInt(param.getPrecedenceFor(h).queryIndex(), 2);
    valuation.setInt(param.getPrecedenceFor(j).queryIndex(), 1);
    valuation.setInt(((IVar)param.getStatusFor(h)).queryIndex(), 3);
    valuation.setInt(((IVar)param.getStatusFor(j)).queryIndex(), 1);
    valuation.setBool(mono.regards(f, 1).queryIndex(), true);
    valuation.setBool(param.getDirectionIsDownVariable().queryIndex(), true);

    HorpoResult result = new HorpoResult(problem, Set.of(0), Set.of(), valuation, param, lst);
    assertTrue(result.queryAnswer() == ProofObject.Answer.YES);
    assertTrue(result.isStrictlyOriented(0));
    assertFalse(result.isStrictlyOriented(1));
    assertTrue(result.isStrictlyOriented(0));
    assertFalse(result.isStrictlyOriented(2));
    assertTrue(result.precedence(f, g) == -1);
    assertTrue(result.precedence(f, j) == 0);
    assertTrue(result.precedence(h, g) == 2);
    assertTrue(result.status(h).equals("Mul_3"));
    assertTrue(result.status(g).equals("Lex"));
    assertTrue(result.status(j).equals("Lex"));
    assertTrue(result.regards(f, 1));
    assertTrue(result.regards(g, 1));
    assertTrue(result.regards(h, 2));
    assertTrue(result.stronglyMonotonic());
    OutputModule o = DefaultOutputModule.createUnicodeModule(trs);
    result.justify(o);
    assertTrue(o.toString().equals(
      "Constrained HORPO yields:\n\n" +
      "  f(x) ≻ f(x - 1) | x > 0\n" +
      "  g(x) ≽ f(x)\n\n" +
      "We do this using the following settings:\n\n" +
      "* Precedence and status (for non-mentioned symbols the precedence is irrelevant and " +
        "the status is Lex):\n\n" +
      "  h      (status: Mul_3) >\n" +
      "  g      (status: Lex)   >\n" +
      "  f = j  (status: Lex)\n\n" +
      "* Well-founded theory orderings:\n\n" +
      "  ⊐_{Bool} = {(true,false)}\n" +
      "  ⊐_{Int}  = {(x,y) | x > -100 ∧ x > y }\n\n" +
      "* Monotonicity requirements: this is a strongly monotonic reduction pair " +
      "(all arguments of function symbols were regarded).\n\n"));
  }

  @Test
  public void testNonStrictProof() {
    TRS trs = makeTrs("f :: Int -> Int g :: Int -> Int h :: Int -> Int -> Int\n" +
                      "f(x) -> f(x-1) | x > 0 g(x) -> f(x)");
    SmtProblem smt = new SmtProblem();
    Monotonicity mono = new ArgumentFilter(smt);
    OrderingProblem problem = new OrderingProblem(trs, mono);
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      Rule r = trs.queryRule(i);
      problem.requireEither(new OrderingRequirement(r, OrderingRequirement.Relation.Strict), i * 2);
    }
    HorpoParameters param = new HorpoParameters(3, smt);
    HorpoConstraintList lst = new HorpoConstraintList(new TermPrinter(Set.of()), smt);
    Valuation valuation = new Valuation();
    FunctionSymbol f = trs.lookupSymbol("f");
    FunctionSymbol g = trs.lookupSymbol("g");
    FunctionSymbol h = trs.lookupSymbol("h");
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    valuation.setInt(param.getPrecedenceFor(f).queryIndex(), 1);
    valuation.setInt(param.getPrecedenceFor(g).queryIndex(), 2);
    valuation.setInt(param.getPrecedenceFor(h).queryIndex(), 2);
    valuation.setInt(param.getPrecedenceFor(plus).queryIndex(), -3);
    valuation.setInt(((IVar)param.getStatusFor(h)).queryIndex(), 1);
    valuation.setInt(((IVar)param.getStatusFor(plus)).queryIndex(), 2);
    valuation.setBool(mono.regards(f, 1).queryIndex(), true);
    valuation.setBool(mono.regards(g, 1).queryIndex(), false);
    valuation.setBool(mono.regards(h, 2).queryIndex(), false);
    valuation.setBool(mono.regards(plus, 1).queryIndex(), true);
    valuation.setBool(mono.regards(plus, 2).queryIndex(), true);
    valuation.setBool(param.getDirectionIsDownVariable().queryIndex(), false);
    HorpoResult result = new HorpoResult(problem, Set.of(1), Set.of(), valuation, param, lst);
    assertTrue(result.queryAnswer() == ProofObject.Answer.YES);
    assertFalse(result.isStrictlyOriented(0));
    assertTrue(result.isStrictlyOriented(1));
    assertTrue(result.precedence(f, g) == -1);
    assertTrue(result.precedence(h, g) == 0);
    assertTrue(result.precedence(plus, f) == -4);
    assertTrue(result.status(h).equals("Lex"));
    assertTrue(result.status(g).equals("Lex"));
    assertTrue(result.status(plus).equals("Mul_2"));
    assertTrue(result.regards(f, 1));
    assertFalse(result.regards(g, 1));
    assertFalse(result.regards(h, 2));
    assertTrue(result.regards(plus, 1));
    assertTrue(result.regards(plus, 2));
    assertFalse(result.stronglyMonotonic());
    OutputModule o = DefaultOutputModule.createUnicodeModule(trs);
    result.justify(o);
    assertTrue(o.toString().equals(
      "Constrained HORPO yields:\n\n" +
      "  f(x) ≽ f(x - 1) | x > 0\n" +
      "  g(x) ≽ f(x)\n\n" +
      "We do this using the following settings:\n\n" +
      "* Precedence and status (for non-mentioned symbols the precedence is irrelevant and the status is Lex):\n\n" +
      "  g = h  (status: Lex)   >\n" +
      "  f      (status: Lex)   >\n" +
      "  +      (status: Mul_2)\n\n" +
      "* Well-founded theory orderings:\n\n" +
      "  ⊐_{Bool} = {(true,false)}\n" +
      "  ⊐_{Int}  = {(x,y) | x < 3 ∧ x < y }\n\n" +
      "* Regarded arguments:\n\n" +
      "  + 1 2 \n" +
      "  f 1 \n\n"));
  }
}

