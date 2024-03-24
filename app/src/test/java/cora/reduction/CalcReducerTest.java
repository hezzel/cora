/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.reduction;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import charlie.types.TypeFactory;
import charlie.terms.*;

public class CalcReducerTest {
  private Term plus() { return TheoryFactory.plusSymbol; }
  private Term v(int i) { return TheoryFactory.createValue(i); }
  private Term v(boolean b) { return TheoryFactory.createValue(b); }

  @Test
  public void testBasics() {
    ReduceObject scheme = new CalcReducer();
    assertTrue(scheme.toString().equals(
      "calc : f(x1,...,xk) → y [f(x1,...,xk) = y] for f ∈ Σ_{theory}"));
  }

  @Test
  public void testBasicCalcReducer() {
    ReduceObject scheme = new CalcReducer();

    // 1 + 1
    Term t = plus().apply(v(1)).apply(v(1));
    assertTrue(scheme.applicable(t));
    assertTrue(scheme.apply(t).equals(v(2)));

    // true ∧ false
    t = TheoryFactory.andSymbol.apply(v(true)).apply(v(false));
    assertTrue(scheme.applicable(t));
    assertTrue(scheme.apply(t).equals(v(false)));
  }

  @Test
  public void testTheoryTermButNotApplicableAtTop() {
    ReduceObject scheme = new CalcReducer();
    // 0 + 1 < 3
    Term t = TheoryFactory.smallerSymbol.apply(plus().apply(v(0)).apply(v(1))).apply(v(3));
    assertFalse(scheme.applicable(t));
    assertTrue(scheme.apply(t) == null);
  }

  @Test
  public void testPartiallyApplied() {
    ReduceObject scheme = new CalcReducer();
    // *(0)
    Term t = TheoryFactory.timesSymbol.apply(v(0));
    assertFalse(scheme.applicable(t));
    assertTrue(scheme.apply(t) == null);
  }

  @Test
  public void testApplyToValue() {
    ReduceObject scheme = new CalcReducer();
    // true
    Term t = v(true);
    assertFalse(scheme.applicable(t));
    assertTrue(scheme.apply(t) == null);
  }

  @Test
  public void testCalcReducerulationSymbolOnVariable() {
    ReduceObject scheme = new CalcReducer();
    // 0 > x
    Term t = TheoryFactory.greaterSymbol.apply(v(0)).apply(TermFactory.createVar(
      v(0).queryType()));
    assertFalse(scheme.applicable(t));
    assertTrue(scheme.apply(t) == null);
  }

  @Test
  public void testVariableAppliedToValues() {
    ReduceObject scheme = new CalcReducer();
    // X(0, 1)
    Term x = TermFactory.createBinder("X", plus().queryType());
    Term t = x.apply(v(0)).apply(v(1));
    assertFalse(scheme.applicable(t));
    assertTrue(scheme.apply(t) == null);
  }

  @Test
  public void testFakeCalcReducerulation() {
    ReduceObject scheme = new CalcReducer();
    // plus(37, 42)
    Term f = TermFactory.createConstant("+", plus().queryType());
    Term t = f.apply(v(37)).apply(v(42));
    assertFalse(scheme.applicable(t));
    assertTrue(scheme.apply(t) == null);
  }
}

