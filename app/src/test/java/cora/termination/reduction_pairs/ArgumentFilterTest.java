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
import java.util.function.BiFunction;

import charlie.util.Pair;
import charlie.types.Type;
import charlie.terms.FunctionSymbol;
import charlie.terms.TermFactory;
import charlie.terms.TheoryFactory;
import charlie.trs.TRS;
import charlie.smt.BVar;
import charlie.smt.IVar;
import charlie.smt.Valuation;
import charlie.smt.SmtProblem;
import charlie.parser.CoraParser;

public class ArgumentFilterTest {
  private Type type(String txt) {
    return CoraParser.readType(txt);
  }

  @Test
  public void testRegardsInEmptyFilter() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    SmtProblem prob = new SmtProblem();
    ArgumentFilter pi = ArgumentFilter.createEmptyFilter(prob);
    BVar x = pi.regards(f, 1);
    BVar y = pi.regards(f, 2);
    assertTrue(x == y);
    y = pi.regards(g, 2);
    assertTrue(x == y);
    y = pi.regards(plus, 1);
    assertTrue(x == y);
    assertTrue(x.queryName().equals("[alwaystrue]"));
    assertTrue(pi.getRegardedArguments(null).apply(f, 3));
    assertTrue(pi.getRegardedArguments(null).apply(g, 1));
  }

  @Test
  public void testRegardsInNormalFilter() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    SmtProblem prob = new SmtProblem();
    ArgumentFilter filter = new ArgumentFilter(prob);
    BVar x = filter.regards(f, 1);
    assertTrue(x.queryName().equals("[regards{f,1}]"));
    BVar y = filter.regards(f, 3);
    assertTrue(x != y);
    assertTrue(y.queryName().equals("[regards{f,3}]"));
    y = filter.regards(g, 1);
    assertTrue(x != y);
    assertTrue(y.queryName().equals("[regards{g,1}]"));
    x = filter.regards(plus, 1);
    y = filter.regards(plus, 2);
    assertTrue(x != y);
  }

  @Test
  public void testForceEmpty() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    SmtProblem prob = new SmtProblem();
    ArgumentFilter filter = new ArgumentFilter(prob);
    BVar x = filter.regards(f, 1);
    assertTrue(x.queryName().equals("[regards{f,1}]"));
    BVar y = filter.regards(f, 3);
    assertTrue(y.queryName().equals("[regards{f,3}]"));
    filter.forceEmpty();
    y = filter.regards(g, 1);
    assertTrue(y.queryName().equals("[alwaystrue]"));
    assertTrue(prob.toString().equals(
      "[regards{f,1}]\n" +
      "[regards{f,3}]\n" +
      "[alwaystrue]\n"));
  }

  @Test
  public void testForceEmptyAfterEverythingRegardedVariableWasChecked() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    SmtProblem prob = new SmtProblem();
    ArgumentFilter filter = new ArgumentFilter(prob);
    BVar x = filter.regards(f, 1);
    assertTrue(x.queryName().equals("[regards{f,1}]"));
    assertTrue(prob.toString().equals(""));
    BVar e = filter.regardsEverything();
    assertTrue(prob.toString().equals("![regardsall] or [regards{f,1}]\n"));
    BVar y = filter.regards(f, 3);
    assertTrue(y.queryName().equals("[regards{f,3}]"));
    assertTrue(prob.toString().equals(
      "![regardsall] or [regards{f,1}]\n" +
      "![regardsall] or [regards{f,3}]\n"));
    filter.forceEmpty();
    y = filter.regards(g, 1);
    assertTrue(y == e);
    assertTrue(prob.toString().equals(
      "![regardsall] or [regards{f,1}]\n" +
      "![regardsall] or [regards{f,3}]\n" +
      "[regardsall]\n"));
  }

  @Test
  public void testGetFilterData() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    FunctionSymbol h = TermFactory.createConstant("h", type("Int -> Int"));
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    SmtProblem prob = new SmtProblem();
    ArgumentFilter filter = new ArgumentFilter(prob);
    BVar a = filter.regards(g, 1);
    BVar b = filter.regards(g, 2);
    BVar c = filter.regards(plus, 2);
    BVar d = filter.regards(h, 1);
    Valuation valuation = new Valuation();
    valuation.setBool(a.queryIndex(), true);
    valuation.setBool(c.queryIndex(), true);
    valuation.setBool(d.queryIndex(), false);
    BiFunction<FunctionSymbol,Integer,Boolean> regarded = filter.getRegardedArguments(valuation);
    assertTrue(regarded.apply(g, 1));
    assertFalse(regarded.apply(g, 2));
    assertTrue(regarded.apply(plus, 1));
    assertTrue(regarded.apply(plus, 2));
    assertFalse(regarded.apply(h, 1));
    assertTrue(regarded.apply(h, 2));
    valuation.setBool(d.queryIndex(), true);
    assertFalse(regarded.apply(h, 1));
    regarded = filter.getRegardedArguments(valuation);
    assertTrue(regarded.apply(h, 1));
  }

  @Test
  public void testEverythingIsRegarded() {
    SmtProblem prob = new SmtProblem();
    ArgumentFilter pi = new ArgumentFilter(prob);
    Valuation valuation = new Valuation();
    assertTrue(pi.everythingIsRegarded(valuation));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    BVar a = pi.regards(g, 1);
    assertFalse(pi.everythingIsRegarded(valuation));
    valuation.setBool(a.queryIndex(), true);
    assertTrue(pi.everythingIsRegarded(valuation));
  }
}

