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

package cora.termination.reduction_pairs;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import java.util.ArrayList;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.terms.FunctionSymbol;
import charlie.terms.TermFactory;
import charlie.terms.TheoryFactory;
import charlie.trs.TRS;
import charlie.smt.BVar;
import charlie.smt.IVar;
import charlie.smt.Valuation;
import charlie.parser.CoraParser;

public class HorpoParametersTest {
  private Type type(String txt) {
    return CoraParser.readType(txt);
  }

  @Test
  public void testIntegerBound() {
    HorpoParameters horpo = new HorpoParameters(37, true);
    assertTrue(horpo.queryIntegerBound() == 37);
    BVar x = horpo.getDirectionIsDownVariable();
    assertTrue(x.toString().equals("[down]"));
    assertTrue(x == horpo.getDirectionIsDownVariable());
  }

  @Test
  public void testPrecedenceFor() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    FunctionSymbol minus = TheoryFactory.minusSymbol;
    HorpoParameters horpo = new HorpoParameters(40, false);
    IVar fx = horpo.getPrecedenceFor(f);
    IVar mx = horpo.getPrecedenceFor(minus);
    IVar gx = horpo.getPrecedenceFor(g);
    assertTrue(horpo.getPrecedenceFor(f) == fx);
    FunctionSymbol gg = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    assertTrue(gx == horpo.getPrecedenceFor(gg));
    assertTrue(horpo.queryProblem().toString().equals(
      "[alwaystrue]\n" +
      "[pred(f)] >= 0\n" +
      "0 >= 1 + [pred(-)]\n" +
      "[pred(g)] >= 0\n"));
  }

  @Test
  public void testStatusFor() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    HorpoParameters horpo = new HorpoParameters(3000, true);
    assertTrue(horpo.getStatusFor(f).toString().equals("1"));
    assertTrue(horpo.getStatusFor(g) == horpo.getStatusFor(g));
    assertTrue(horpo.getStatusFor(plus) != null);
    assertTrue(horpo.queryProblem().toString().equals(
      "[alwaystrue]\n" +
      "[stat(g)] >= 1\n" +
      "2 >= [stat(g)]\n" +
      "[pred(g)] >= 0\n" +
      "[stat(+)] >= 1\n" +
      "2 >= [stat(+)]\n" +
      "0 >= 1 + [pred(+)]\n"));
  }

  @Test
  public void testRegardsInStrict() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    HorpoParameters horpo = new HorpoParameters(3000, true);
    BVar x = horpo.getRegardsVariableFor(f, 1);
    BVar y = horpo.getRegardsVariableFor(f, 2);
    assertTrue(x == y);
    y = horpo.getRegardsVariableFor(g, 2);
    assertTrue(x == y);
    y = horpo.getRegardsVariableFor(plus, 1);
    assertTrue(x == y);
    assertTrue(x.queryName().equals("[alwaystrue]"));
  }

  @Test
  public void testRegardsInWeak() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    HorpoParameters horpo = new HorpoParameters(3000, false);
    BVar x = horpo.getRegardsVariableFor(f, 1);
    assertTrue(x.queryName().equals("[regards(f,1)]"));
    BVar y = horpo.getRegardsVariableFor(f, 3);
    assertTrue(x != y);
    assertTrue(y.queryName().equals("[regards(f,3)]"));
    y = horpo.getRegardsVariableFor(g, 1);
    assertTrue(x != y);
    assertTrue(y.queryName().equals("[regards(g,1)]"));
    x = horpo.getRegardsVariableFor(plus, 1);
    y = horpo.getRegardsVariableFor(plus, 2);
    assertTrue(x == y);
    assertTrue(x.queryName().equals("[alwaystrue]"));
  }

  @Test
  public void testGetSymbolData() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    HorpoParameters horpo = new HorpoParameters(3000, false);
    IVar x = horpo.getPrecedenceFor(f);
    IVar y = horpo.getPrecedenceFor(g);
    IVar a = (IVar)horpo.getStatusFor(g);
    horpo.getStatusFor(f);
    IVar z = horpo.getPrecedenceFor(plus);
    IVar b = (IVar)horpo.getStatusFor(plus);
    Valuation valuation = new Valuation();
    valuation.setInt(x.queryIndex(), 3);
    valuation.setInt(y.queryIndex(), 3);
    valuation.setInt(z.queryIndex(), -2);
    valuation.setInt(a.queryIndex(), 2);
    valuation.setInt(b.queryIndex(), 1);
    ArrayList<HorpoParameters.SymbolData> data = horpo.getSymbolData(valuation);
    assertTrue(data.get(0).symbol().equals("g"));
    assertTrue(data.get(0).prec() == 3);
    assertTrue(data.get(0).stat() == 2);
    assertTrue(data.get(1).symbol().equals("f"));
    assertTrue(data.get(1).prec() == 3);
    assertTrue(data.get(1).stat() == 1);
    assertTrue(data.get(2).symbol().equals("+"));
    assertTrue(data.get(2).prec() == -2);
    assertTrue(data.get(2).stat() == 1);
  }

  @Test
  public void testGetFilterData() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    FunctionSymbol h = TermFactory.createConstant("h", type("Int -> Int"));
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    HorpoParameters horpo = new HorpoParameters(3000, false);
    IVar x = horpo.getPrecedenceFor(f);
    IVar y = horpo.getPrecedenceFor(h);
    BVar a = horpo.getRegardsVariableFor(g, 1);
    BVar b = horpo.getRegardsVariableFor(g, 2);
    BVar c = horpo.getRegardsVariableFor(plus, 1);
    BVar d = horpo.getRegardsVariableFor(h, 1);
    assertTrue(c.queryName().equals("[alwaystrue]"));
    Valuation valuation = new Valuation();
    valuation.setInt(x.queryIndex(), 7);
    valuation.setInt(y.queryIndex(), 0);
    valuation.setBool(a.queryIndex(), true);
    ArrayList<Pair<String,Integer>> disregarded = horpo.getDisregardedArguments(valuation);
    assertTrue(disregarded.size() == 2);
    assertTrue(disregarded.get(0).fst().equals("g"));
    assertTrue(disregarded.get(0).snd() == 2);
    assertTrue(disregarded.get(1).fst().equals("h"));
    assertTrue(disregarded.get(1).snd() == 1);
  }
}

