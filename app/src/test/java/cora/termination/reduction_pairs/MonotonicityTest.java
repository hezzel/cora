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

public class MonotonicityTest {
  private Type type(String txt) {
    return CoraParser.readType(txt);
  }

  @Test
  public void testRegardsInStrict() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    SmtProblem prob = new SmtProblem();
    Monotonicity mono = new StrongMonotonicity(prob);
    assertTrue(mono.stronglyMonotonic());
    BVar x = mono.regards(f, 1);
    BVar y = mono.regards(f, 2);
    assertTrue(x == y);
    y = mono.regards(g, 2);
    assertTrue(x == y);
    y = mono.regards(plus, 1);
    assertTrue(x == y);
    assertTrue(x.queryName().equals("[alwaystrue]"));
    assertTrue(mono.getRegardedArguments(null).apply(f, 3));
    assertTrue(mono.getRegardedArguments(null).apply(g, 1));
  }

  @Test
  public void testRegardsInSymbol() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    SmtProblem prob = new SmtProblem();
    Monotonicity mono = new ArgumentFilter(prob);
    BVar x = mono.regards(f, 1);
    assertTrue(x.queryName().equals("[regards{f,1}]"));
    BVar y = mono.regards(f, 3);
    assertTrue(x != y);
    assertTrue(y.queryName().equals("[regards{f,3}]"));
    y = mono.regards(g, 1);
    assertTrue(x != y);
    assertTrue(y.queryName().equals("[regards{g,1}]"));
    x = mono.regards(plus, 1);
    y = mono.regards(plus, 2);
    assertTrue(x != y);
  }

  @Test
  public void testGetFilterData() {
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    FunctionSymbol h = TermFactory.createConstant("h", type("Int -> Int"));
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    SmtProblem prob = new SmtProblem();
    ArgumentFilter mono = new ArgumentFilter(prob);
    BVar a = mono.regards(g, 1);
    BVar b = mono.regards(g, 2);
    BVar c = mono.regards(plus, 2);
    BVar d = mono.regards(h, 1);
    Valuation valuation = new Valuation();
    valuation.setBool(a.queryIndex(), true);
    valuation.setBool(c.queryIndex(), true);
    valuation.setBool(d.queryIndex(), false);
    BiFunction<FunctionSymbol,Integer,Boolean> regarded = mono.getRegardedArguments(valuation);
    assertTrue(regarded.apply(g, 1));
    assertFalse(regarded.apply(g, 2));
    assertFalse(regarded.apply(plus, 1));
    assertTrue(regarded.apply(plus, 2));
    assertFalse(regarded.apply(h, 1));
    assertFalse(regarded.apply(h, 2));
    valuation.setBool(d.queryIndex(), true);
    assertFalse(regarded.apply(h, 1));
    regarded = mono.getRegardedArguments(valuation);
    assertTrue(regarded.apply(h, 1));
  }
}

