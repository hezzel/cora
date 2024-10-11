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

import java.util.ArrayList;
import java.util.TreeSet;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.terms.FunctionSymbol;
import charlie.terms.TermFactory;
import charlie.terms.TheoryFactory;
import charlie.trs.TRS;
import charlie.smt.*;
import charlie.parser.CoraParser;
import cora.termination.reduction_pairs.ArgumentFilter;

public class HorpoParametersTest {
  private Type type(String txt) {
    return CoraParser.readType(txt);
  }

  @Test
  public void testBasics() {
    SmtProblem smt = new SmtProblem();
    HorpoParameters horpo = new HorpoParameters(37, new TreeSet<FunctionSymbol>(),
                                                new ArgumentFilter(smt), smt);
    assertTrue(horpo.queryIntegerBound() == 37);
    BVar x = horpo.getDirectionIsDownVariable();
    assertTrue(x.toString().equals("[down]"));
    assertTrue(x == horpo.getDirectionIsDownVariable());
  }

  @Test
  public void testSetup() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    FunctionSymbol minus = TheoryFactory.minusSymbol;
    FunctionSymbol three = TheoryFactory.createValue(3);
    SmtProblem prob = new SmtProblem();
    TreeSet<FunctionSymbol> set = new TreeSet<FunctionSymbol>();
    set.add(f);
    set.add(g);
    set.add(minus);
    set.add(three);
    HorpoParameters horpo = new HorpoParameters(40, set, new ArgumentFilter(prob), prob);
    assertTrue(prob.toString().equals(
      // precedence: 1 ≤ pred(h) ≤ 4 for h ∈ {f,g,minus}, and pred(3) = 0
      "[pred(-)] >= 1\n" +
      "4 >= [pred(-)]\n" +
      "[zero] = 0\n" +
      "[pred(f)] >= 1\n" +
      "4 >= [pred(f)]\n" +
      "[pred(g)] >= 1\n" +
      "4 >= [pred(g)]\n" +
      // permutation: (¬regards{h,i} → π{h}(i) = 0) ∧ (regards{h,i} → π{h}(i) ≥ 1) ∧ π{h}(i) ≤ ar(h)
      "[regards{-,1}] or ([pi{-}(1)] = 0)\n" +
      "![regards{-,1}] or ([pi{-}(1)] = 1)\n" +
      "[regards{f,1}] or ([pi{f}(1)] = 0)\n" +
      "![regards{f,1}] or ([pi{f}(1)] = 1)\n" +
      "[regards{g,1}] or ([pi{g}(1)] = 0)\n" +
      "![regards{g,1}] or ([pi{g}(1)] >= 1)\n" +
      "2 >= [pi{g}(1)]\n" +
      "[regards{g,2}] or ([pi{g}(2)] = 0)\n" +
      "![regards{g,2}] or ([pi{g}(2)] >= 1)\n" +
      "2 >= [pi{g}(2)]\n" +
      "([pi{g}(2)] # [pi{g}(1)]) or ([pi{g}(2)] = 1)\n"));
  }

  @Test
  public void testPrecedence() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    SmtProblem prob = new SmtProblem();
    TreeSet<FunctionSymbol> set = new TreeSet<FunctionSymbol>();
    set.add(f);
    set.add(g);
    HorpoParameters horpo = new HorpoParameters(40, set, new ArgumentFilter(prob), prob);
    IVar fx = horpo.getPrecedence(f);
    IVar gx = horpo.getPrecedence(g);
    assertFalse(fx.equals(gx));
    assertTrue(horpo.getPrecedence(f) == fx);
    FunctionSymbol gg = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    assertTrue(gx == horpo.getPrecedence(gg));
  }

  @Test
  public void testPermutation() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    SmtProblem prob = new SmtProblem();
    TreeSet<FunctionSymbol> set = new TreeSet<FunctionSymbol>();
    set.add(f);
    set.add(g);
    HorpoParameters horpo = new HorpoParameters(40, set, new ArgumentFilter(prob), prob);
    IVar f1 = horpo.getPermutation(f, 1);
    IVar g1 = horpo.getPermutation(g, 1);
    assertTrue(g1 == horpo.getPermutation(g, 1));
    assertFalse(g1 == horpo.getPermutation(g, 2));
    assertFalse(f1 == g1);
  }

  @Test
  public void testGetSymbolData() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    FunctionSymbol h = TermFactory.createConstant("h", type("Int -> Int -> Int -> Int"));
    FunctionSymbol three = TheoryFactory.createValue(3);
    SmtProblem prob = new SmtProblem();
    TreeSet<FunctionSymbol> set = new TreeSet<FunctionSymbol>();
    set.add(f);
    set.add(g);
    set.add(h);
    set.add(three);
    set.add(TheoryFactory.createValue(4));
    HorpoParameters horpo = new HorpoParameters(40, set, new ArgumentFilter(prob), prob);
    IVar x = horpo.getPrecedence(f);
    IVar y = horpo.getPrecedence(g);
    IVar z = horpo.getPrecedence(h);
    IVar t = horpo.getPrecedence(three);
    IVar pf1 = horpo.getPermutation(f, 1);
    IVar pg1 = horpo.getPermutation(g, 1);
    IVar pg2 = horpo.getPermutation(g, 2);
    IVar ph1 = horpo.getPermutation(h, 1);
    IVar ph2 = horpo.getPermutation(h, 2);
    IVar ph3 = horpo.getPermutation(h, 3);
    Valuation valuation = new Valuation();
    valuation.setInt(x.queryIndex(), 3);
    valuation.setInt(y.queryIndex(), 3);
    valuation.setInt(z.queryIndex(), 2);
    valuation.setInt(t.queryIndex(), 0);
    valuation.setInt(pf1.queryIndex(), 1);
    valuation.setInt(pg1.queryIndex(), 0);
    valuation.setInt(pg2.queryIndex(), 1);
    valuation.setInt(ph1.queryIndex(), 1);
    valuation.setInt(ph2.queryIndex(), 3);
    valuation.setInt(ph3.queryIndex(), 1);
    ArrayList<HorpoParameters.SymbolData> data = horpo.getSymbolData(valuation);
    assertTrue(data.size() == 5);
    assertTrue(data.get(0).toString().equals("f : [ { 1 } ] (3)"));
    assertTrue(data.get(1).toString().equals("g : [ { 2 } _ ] (3)"));
    assertTrue(data.get(2).toString().equals("h : [ { 1 3 } _ 2 ] (2)"));
    assertTrue(data.get(3).toString().equals("3 : [ { } ] (0)"));
    assertTrue(data.get(4).toString().equals("4 : [ { } ] (0)"));
  }
}

