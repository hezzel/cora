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

import charlie.types.Type;
import charlie.terms.FunctionSymbol;
import charlie.terms.TermFactory;
import charlie.terms.TheoryFactory;
import charlie.trs.TRS;
import charlie.smt.BVar;
import charlie.smt.IVar;
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
      "[stat(+)] >= 1\n" +
      "2 >= [stat(+)]\n"));
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
}

