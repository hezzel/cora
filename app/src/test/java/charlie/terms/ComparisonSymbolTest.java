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

package charlie.terms;

import java.util.ArrayList;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import charlie.exceptions.*;
import charlie.types.TypeFactory;
import charlie.types.Type;

public class ComparisonSymbolTest extends TermTestFoundation {
  @Test
  public void testGeqBasics() {
    CalculationSymbol s = TheoryFactory.geqSymbol;
    assertTrue(s.queryType().toString().equals("Int → Int → Bool"));
    assertTrue(s.queryInfixPriority() == CalculationSymbol.INFIX_COMPARISON);
    assertTrue(s.queryName().equals("≥"));
    assertTrue(s.toString().equals("[≥]"));
    assertTrue(s.toUniqueString().equals("≥{Int → Int → Bool}#calc"));
    assertTrue(s.queryArity() == 2);
  }

  @Test
  public void testLeqBasics() {
    CalculationSymbol s = TheoryFactory.leqSymbol;
    assertTrue(s.queryType().toString().equals("Int → Int → Bool"));
    assertTrue(s.queryInfixPriority() == CalculationSymbol.INFIX_COMPARISON);
    assertTrue(s.queryName().equals("≤"));
    assertTrue(s.toString().equals("[≤]"));
    assertTrue(s.toUniqueString().equals("≤{Int → Int → Bool}#calc"));
    assertTrue(s.queryArity() == 2);
  }

  @Test
  public void testGreaterBasics() {
    CalculationSymbol s = TheoryFactory.greaterSymbol;
    assertTrue(s.queryName().equals(">"));
    assertTrue(s.toString().equals("[>]"));
    assertTrue(s.toUniqueString().equals(">{Int → Int → Bool}#calc"));
  }

  @Test
  public void testSmallerBasics() {
    CalculationSymbol s = TheoryFactory.smallerSymbol;
    assertTrue(s.queryName().equals("<"));
    assertTrue(s.toString().equals("[<]"));
    assertTrue(s.toUniqueString().equals("<{Int → Int → Bool}#calc"));
  }

  @Test
  public void testSimpleToString() {
    CalculationSymbol s = TheoryFactory.greaterSymbol;

    Value v = new IntegerValue(12);
    assertTrue(s.apply(v).toString().equals("[>](12)"));

    Var w = new Var("x", TypeFactory.intSort);
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(v);
    args.add(w);
    assertTrue(s.apply(args).toString().equals("12 > x"));
  }

  @Test
  public void testToStringWithComplexChildren() {
    CalculationSymbol s = TheoryFactory.geqSymbol;
    Variable x = new Var("x", TypeFactory.intSort);
    Variable y = new Binder("y", TypeFactory.intSort);
    Term t = s.apply(new Application(TheoryFactory.plusSymbol, x, y))
              .apply(new Application(TheoryFactory.timesSymbol, y, x));
    assertTrue(t.toString().equals("x + y ≥ y * x"));
  }

  @Test
  public void testToStringWithNot() {
    CalculationSymbol s = TheoryFactory.greaterSymbol;
    Variable x = new Var("x", TypeFactory.intSort);
    Variable y = new Binder("y", TypeFactory.intSort);
    Term t = s.apply(new Application(TheoryFactory.plusSymbol, x, y)).apply(x);
    t = TheoryFactory.notSymbol.apply(t);
    assertTrue(t.toString().equals("¬(x + y > x)"));
  }

  @Test
  public void testEqualityEquality() {
    FunctionSymbol a = TheoryFactory.smallerSymbol;
    FunctionSymbol b = TheoryFactory.leqSymbol;
    FunctionSymbol c = new Constant("<", a.queryType());
    assertTrue(a.equals(TheoryFactory.smallerSymbol));
    assertFalse(a.equals(b));
    assertFalse(a.equals(c));
    assertFalse(c.equals(a));
  }
}
