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

public class PlusTimesMinusSymbolTest extends TermTestFoundation {
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
  public void testMinusBasics() {
    CalculationSymbol m = new MinusSymbol();
    assertTrue(m.queryType().toString().equals("Int ⇒ Int"));
    assertTrue(m.queryInfixPriority() == CalculationSymbol.INFIX_MINUS);
    assertTrue(m.queryName().equals("-"));
    assertTrue(m.toString().equals("-"));
    assertTrue(m.toUniqueString().equals("-"));
    assertTrue(m.queryArity() == 1);
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
  public void testSimpleMinusToString() {
    CalculationSymbol f = new MinusSymbol();
    assertTrue(f.toString().equals("-"));
    Value v = new IntegerValue(3);
    assertTrue(f.apply(v).toString().equals("-3"));
    Var x = new Var("x", TypeFactory.intSort);
    assertTrue(f.apply(x).toString().equals("-x"));
  }

  @Test
  public void testMinusWithNegativeValue() {
    CalculationSymbol f = new MinusSymbol();
    assertTrue(f.toString().equals("-"));
    Value v = new IntegerValue(-3);
    assertTrue(f.apply(v).toString().equals("-(-3)"));
  }

  @Test
  public void testMinusWithComplexArgument() {
    CalculationSymbol m = new MinusSymbol();
    CalculationSymbol p = new PlusSymbol();
    CalculationSymbol t = new TimesSymbol();
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Term s = m.apply(p.apply(x).apply(y));
    assertTrue(s.toString().equals("-(x + y)"));
    s = m.apply(t.apply(x).apply(y));
    assertTrue(s.toString().equals("-(x * y)"));
  }

  @Test
  public void testPrintPlusNegativeValue() {
    Var x = new Var("x", TypeFactory.intSort);
    Term s = new Application(new PlusSymbol(), x, new IntegerValue(-3));
    assertTrue(s.toString().equals("x - 3"));
  }

  @Test
  public void testPrintPlusNegativeAddition() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Var z = new Var("z", TypeFactory.intSort);
    CalculationSymbol p = new PlusSymbol();
    Term s = new Application(p, x, new Application(new MinusSymbol(),
      new Application(p, y, z)));
    assertTrue(s.toString().equals("x - (y + z)"));
  }

  @Test
  public void testPrintPlusNegativeMultiplication() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Var z = new Var("z", TypeFactory.intSort);
    Term s = new Application(new PlusSymbol(), x, new Application(new MinusSymbol(),
      new Application(new TimesSymbol(), y, z)));
    assertTrue(s.toString().equals("x - y * z"));
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
    CalculationSymbol minus = new MinusSymbol();
    Term a = new Application(times, new IntegerValue(1), new Application(plus, x, y));
    Term b = new Application(plus, x, new IntegerValue(-3));
    Term c = new Application(plus, y, minus.apply(new Application(times, x, new IntegerValue(0))));
    Term d = new Application(plus, b, new Application(plus, c, z));
    Term s = new Application(times, a, d);
    assertTrue(s.toString().equals("1 * (x + y) * (x - 3 + (y - x * 0 + z))"));
  }

  @Test
  public void testPlusTimesMinusEquality() {
    FunctionSymbol plus = new PlusSymbol();
    FunctionSymbol times = new TimesSymbol();
    FunctionSymbol minus = new MinusSymbol();
    Type i = TypeFactory.intSort;
    FunctionSymbol fakeplus = new Constant("+", arrowType(i, arrowType(i, i)));
    FunctionSymbol faketimes = new Constant("*", arrowType(i, arrowType(i, i)));
    FunctionSymbol fakeminus = new Constant("-", arrowType(i, i));
    assertTrue(plus.equals(new PlusSymbol()));
    assertFalse(plus.equals(fakeplus));
    assertFalse(plus.equals(times));
    assertFalse(plus.equals(minus));
    assertFalse(fakeplus.equals(plus));
    assertFalse(plus.equals(null)); // no error
    Term a = times;
    Term b = faketimes;
    assertFalse(a.equals(b));
    assertFalse(b.equals(a));
    assertTrue(a.equals(a));
    assertFalse(minus.equals(fakeminus));
    assertFalse(fakeminus.equals(minus));
    assertTrue(minus.equals(minus));
  }
}
