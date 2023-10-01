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

public class PlusTimesSymbolTest extends TermTestFoundation {
  @Test
  public void testPlusBasics() {
    CalculationSymbol p = new PlusSymbol();
    assertTrue(p.queryType().toString().equals("Int ⇒ Int ⇒ Int"));
    assertTrue(p.queryInfixPriority() == CalculationSymbol.INFIX_PLUS);
    assertTrue(p.queryName().equals("+"));
    assertTrue(p.toString().equals("+"));
    assertTrue(p.toUniqueString().equals("+"));
    assertTrue(p.queryArity() == 2);
  }

  @Test
  public void testTimesBasics() {
    CalculationSymbol t = new TimesSymbol();
    assertTrue(t.queryType().toString().equals("Int ⇒ Int ⇒ Int"));
    assertTrue(t.queryInfixPriority() == CalculationSymbol.INFIX_TIMES);
    assertTrue(t.queryName().equals("*"));
    assertTrue(t.toString().equals("*"));
    assertTrue(t.toUniqueString().equals("*"));
    assertTrue(t.queryArity() == 2);
  }

  @Test
  public void testSimplePlusToString() {
    CalculationSymbol f = new PlusSymbol();
    assertTrue(f.toString().equals("+"));
    Value v = new IntegerValue(3);
    assertTrue(f.apply(v).toString().equals("+(3)"));
    Value w = new IntegerValue(13);
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(v);
    args.add(w);
    assertTrue(f.apply(args).toString().equals("3 + 13"));
  }

  @Test
  public void testSimpleTimesToString() {
    CalculationSymbol f = new TimesSymbol();
    assertTrue(f.toString().equals("*"));
    Value v = new IntegerValue(3);
    assertTrue(f.apply(v).toString().equals("*(3)"));
    Value w = new IntegerValue(13);
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(v);
    args.add(w);
    assertTrue(f.apply(args).toString().equals("3 * 13"));
  }

  @Test
  public void testPrintPlusNegative() {
    Var x = new Var("x", TypeFactory.intSort);
    Term s = new Application(new PlusSymbol(), x, new IntegerValue(-3));
    assertTrue(s.toString().equals("x - 3"));
  }

  @Test
  public void testPlusLeftAssociativity() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Var z = new Var("z", TypeFactory.intSort);
    CalculationSymbol plus = new PlusSymbol();
    Term s = new Application(plus, new Application(plus, x, y), z);
    assertTrue(s.toString().equals("x + y + z"));
  }

  @Test
  public void testPlusNotRightAssociative() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Var z = new Var("z", TypeFactory.intSort);
    CalculationSymbol plus = new PlusSymbol();
    Term s = new Application(plus, x, new Application(plus, y, z));
    assertTrue(s.toString().equals("x + (y + z)"));
  }

  @Test
  public void testTimesLeftAssociativity() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Var z = new Var("z", TypeFactory.intSort);
    CalculationSymbol times = new TimesSymbol();
    Term s = new Application(times, new Application(times, x, y), z);
    assertTrue(s.toString().equals("x * y * z"));
  }

  @Test
  public void testTimesNotRightAssociative() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Var z = new Var("z", TypeFactory.intSort);
    CalculationSymbol times = new TimesSymbol();
    Term s = new Application(times, x, new Application(times, y, z));
    assertTrue(s.toString().equals("x * (y * z)"));
  }

  @Test
  public void testPlusInTimes() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    CalculationSymbol plus = new PlusSymbol();
    CalculationSymbol times = new TimesSymbol();
    Term s = new Application(times, new Application(plus, x, y), new Application(plus, y, x));
    assertTrue(s.toString().equals("(x + y) * (y + x)"));
  }

  @Test
  public void testTimesInPlus() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    CalculationSymbol plus = new PlusSymbol();
    CalculationSymbol times = new TimesSymbol();
    Term s = new Application(plus, new Application(times, x, y), new Application(times, y, x));
    assertTrue(s.toString().equals("x * y + y * x"));
  }

  @Test
  public void testComplexIntegerExpressionToString() {
    // (1 * (x + y)) * ( (x + -3) + ((y + x * 0) + z) )
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Var z = new Var("z", TypeFactory.intSort);
    CalculationSymbol plus = new PlusSymbol();
    CalculationSymbol times = new TimesSymbol();
    Term a = new Application(times, new IntegerValue(1), new Application(plus, x, y));
    Term b = new Application(plus, x, new IntegerValue(-3));
    Term c = new Application(plus, y, new Application(times, x, new IntegerValue(0)));
    Term d = new Application(plus, b, new Application(plus, c, z));
    Term s = new Application(times, a, d);
    assertTrue(s.toString().equals("1 * (x + y) * (x - 3 + (y + x * 0 + z))"));
  }

  @Test
  public void testPlusTimesEquality() {
    FunctionSymbol plus = new PlusSymbol();
    FunctionSymbol times = new TimesSymbol();
    Type i = TypeFactory.intSort;
    FunctionSymbol fakeplus = new Constant("+", arrowType(i, arrowType(i, i)));
    FunctionSymbol faketimes = new Constant("*", arrowType(i, arrowType(i, i)));
    assertTrue(plus.equals(new PlusSymbol()));
    assertFalse(plus.equals(fakeplus));
    assertFalse(plus.equals(times));
    assertFalse(fakeplus.equals(plus));
    assertFalse(plus.equals(null)); // no error
    Term a = times;
    Term b = faketimes;
    assertFalse(a.equals(b));
    assertFalse(b.equals(a));
    assertTrue(a.equals(a));
  }

  @Test
  public void testPlusCalculate() {
    ArrayList<Term> args = new ArrayList<Term>();
    CalculationSymbol p = new PlusSymbol();
    assertTrue(p.calculate(args) == null);  // +()
    args.add(new IntegerValue(3));
    assertTrue(p.calculate(args) == null);  // +(3)
    args.add(new BooleanValue(true));
    assertTrue(p.calculate(args) == null);  // 3 + true
    args.set(1, new Application(p, new IntegerValue(0), new IntegerValue(0)));
    assertTrue(p.calculate(args) == null);  // 3 + (0 + 0)
    args.set(1, new IntegerValue(-7));
    assertTrue(p.calculate(args).equals(new IntegerValue(-4))); // 3 + -7
  }

  @Test
  public void testTimesCalculate() {
    ArrayList<Term> args = new ArrayList<Term>();
    CalculationSymbol t = new TimesSymbol();
    assertTrue(t.calculate(args) == null);  // *()
    args.add(new IntegerValue(3));
    assertTrue(t.calculate(args) == null);  // *(3)
    args.add(new BooleanValue(false));
    assertTrue(t.calculate(args) == null);  // 3 * false
    args.set(1, new Application(t, new IntegerValue(0), new IntegerValue(0)));
    assertTrue(t.calculate(args) == null);  // 3 * (0 * 0)
    args.set(1, new IntegerValue(-7));
    assertTrue(t.calculate(args).equals(new IntegerValue(-21))); // 3 * -7
  }
}
