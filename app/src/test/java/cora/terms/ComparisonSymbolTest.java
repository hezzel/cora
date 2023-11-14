/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.terms;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.exceptions.*;
import cora.types.TypeFactory;
import cora.types.Type;

public class ComparisonSymbolTest extends TermTestFoundation {
  @Test
  public void testGeqBasics() {
    CalculationSymbol s = new ComparisonSymbol(ComparisonSymbol.KIND_GEQ);
    assertTrue(s.queryType().toString().equals("Int ⇒ Int ⇒ Bool"));
    assertTrue(s.queryInfixPriority() == CalculationSymbol.INFIX_COMPARISON);
    assertTrue(s.queryName().equals("≥"));
    assertTrue(s.toString().equals("≥"));
    assertTrue(s.toUniqueString().equals("≥"));
    assertTrue(s.queryArity() == 2);
  }

  @Test
  public void testLeqBasics() {
    CalculationSymbol s = new ComparisonSymbol(ComparisonSymbol.KIND_LEQ);
    assertTrue(s.queryType().toString().equals("Int ⇒ Int ⇒ Bool"));
    assertTrue(s.queryInfixPriority() == CalculationSymbol.INFIX_COMPARISON);
    assertTrue(s.queryName().equals("≤"));
    assertTrue(s.toString().equals("≤"));
    assertTrue(s.toUniqueString().equals("≤"));
    assertTrue(s.queryArity() == 2);
  }

  @Test
  public void testGreaterBasics() {
    CalculationSymbol s = new ComparisonSymbol(ComparisonSymbol.KIND_GRE);
    assertTrue(s.queryName().equals(">"));
    assertTrue(s.toString().equals(">"));
    assertTrue(s.toUniqueString().equals(">"));
  }

  @Test
  public void testSmallerBasics() {
    CalculationSymbol s = new ComparisonSymbol(ComparisonSymbol.KIND_SMA);
    assertTrue(s.queryName().equals("<"));
    assertTrue(s.toString().equals("<"));
    assertTrue(s.toUniqueString().equals("<"));
  }

  @Test
  public void testSimpleToString() {
    CalculationSymbol s = new ComparisonSymbol(ComparisonSymbol.KIND_GRE);

    Value v = new IntegerValue(12);
    assertTrue(s.apply(v).toString().equals(">(12)"));

    Var w = new Var("x", TypeFactory.intSort);
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(v);
    args.add(w);
    assertTrue(s.apply(args).toString().equals("12 > x"));
  }

  @Test
  public void testToStringWithComplexChildren() {
    CalculationSymbol s = new ComparisonSymbol(ComparisonSymbol.KIND_GEQ);
    Variable x = new Var("x", TypeFactory.intSort);
    Variable y = new Binder("y", TypeFactory.intSort);
    Term t = s.apply(new Application(new PlusSymbol(), x, y))
              .apply(new Application(new TimesSymbol(), y, x));
    assertTrue(t.toString().equals("x + y ≥ y * x"));
  }

  @Test
  public void testToStringWithNot() {
    CalculationSymbol s = new ComparisonSymbol(ComparisonSymbol.KIND_GRE);
    Variable x = new Var("x", TypeFactory.intSort);
    Variable y = new Binder("y", TypeFactory.intSort);
    Term t = s.apply(new Application(new PlusSymbol(), x, y)).apply(x);
    t = (new NotSymbol()).apply(t);
    assertTrue(t.toString().equals("¬(x + y > x)"));
  }

  @Test
  public void testEqualityEquality() {
    FunctionSymbol a = new ComparisonSymbol(ComparisonSymbol.KIND_SMA);
    FunctionSymbol b = new ComparisonSymbol(ComparisonSymbol.KIND_LEQ);
    FunctionSymbol c = new Constant("<", a.queryType());
    assertTrue(a.equals(new ComparisonSymbol(ComparisonSymbol.KIND_SMA)));
    assertFalse(a.equals(b));
    assertFalse(a.equals(c));
    assertFalse(c.equals(a));
  }
}
