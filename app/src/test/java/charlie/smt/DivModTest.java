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

package charlie.smt;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class DivModTest {
  @Test
  public void testDivisionBasics() {
    Division division = new Division(new Addition(new IValue(-4), new IVar(1)), new IValue(5));
    assertTrue(division.queryNumerator().equals(new Addition(new IValue(-4), new IVar(1))));
    assertTrue(division.queryDenominator().equals(new IValue(5)));
    assertTrue(division.toSmtString().equals("(div (+ (- 4) i1) 5)"));
    assertTrue(division.toString().equals("(-4 + i1) / 5"));
  }

  @Test
  public void testModuloBasics() {
    Modulo modulo = new Modulo(new CMult(-1, new IVar(2)),
      new Multiplication(new IValue(2), new IVar(3)));
    assertTrue(modulo.queryNumerator().equals(new CMult(-1, new IVar(2))));
    assertTrue(modulo.queryDenominator().equals(new Multiplication(new IValue(2), new IVar(3))));
    assertTrue(modulo.toSmtString().equals("(mod (- i2) (* 2 i3))"));
    assertTrue(modulo.toString().equals("(-i2) % (2 * i3)"));
  }
  
  @Test
  public void testBouteEvaluate() {
    // tests whether divide and modulo follow the definitions by Boute
    for (int num = -5; num <= 5; num++) {
      for (int denom = -3; denom <= 3; denom++) {
        int d = (new Division(new IValue(num), new IValue(denom))).evaluate();
        int m = (new Modulo(new IValue(num), new IValue(denom))).evaluate();
        String situation = "" + num + " / " + denom + " = " + d + " and " +
                                num + " % " + denom + " = " + m;
        if (denom == 0) {
          assertTrue(d == 0, situation + " (div not 0)");
          assertTrue(m == 0, situation + " (mod not 0)");
        }
        else {
          assertTrue(0 <= m, situation + " (mod too small)");
          assertTrue(m < (denom < 0 ? -denom : denom), situation + " (mod too large)");
          assertTrue(d * denom + m == num, situation + " (rule violated)");
        }
      }
    }
  }

  @Test
  public void testCMult() {
    IVar x = new IVar(7);
    IValue c = new IValue(3);
    IntegerExpression d = new Division(x, c);
    IntegerExpression m = new Modulo(x, c);
    assertTrue(d.negate().equals(new CMult(-1, d)));
    assertTrue(m.multiply(3).equals(new CMult(3, m)));
    assertTrue(d.multiply(1).equals(d));
    assertTrue(m.multiply(0).equals(new IValue(0)));
  }

  @Test
  public void testAdd() {
    Division division = new Division(new Addition(new IValue(-4), new IVar(1)), new IValue(5));
    IntegerExpression a = division.add(3);
    IntegerExpression b = division.add(1);
    IntegerExpression c = division.add(0);
    assertTrue(a.toString().equals("3 + (-4 + i1) / 5"));
    assertTrue(a.isSimplified());
    assertTrue(b.toString().equals("1 + (-4 + i1) / 5"));
    assertTrue(b.isSimplified());
    assertTrue(c == division);
    Modulo modulo = new Modulo(new IVar(3), new IValue(-2));
    IntegerExpression d = modulo.add(3);
    assertFalse(d.isSimplified());  // because modulo is not
  }

  @Test
  public void testDivisionComparison() {
    IntegerExpression a = new Division(new IValue(3), new IVar(2));
    IntegerExpression b = new Division(new IValue(3), new IVar(2));
    IntegerExpression c = new Division(new IValue(2), new IVar(3));
    IntegerExpression d = new Division(new IValue(3), new IVar(1));
    IntegerExpression e = new Division(new IValue(4), new IVar(2));
    IntegerExpression f = new Division(new IValue(-3), new IVar(2));
    assertTrue(a.compareTo(b) == 0);
    assertTrue(a.compareTo(c) < 0);
    assertTrue(a.compareTo(d) > 0);
    assertTrue(a.compareTo(e) < 0);
    assertTrue(a.compareTo(f) > 0);
  }

  @Test
  public void testDivisionHashCode() {
    IntegerExpression a = new Division(new IValue(3), new IVar(2));
    IntegerExpression b = new Division(new IValue(3), new IVar(2));
    IntegerExpression c = new Division(new IValue(2), new IVar(3));
    IntegerExpression d = new Division(new IValue(3), new IVar(1));
    IntegerExpression e = new Division(new IValue(4), new IVar(2));
    IntegerExpression f = new Division(new IValue(-3), new IVar(2));
    IntegerExpression g = new Modulo(new IValue(3), new IVar(2));
    assertTrue(a.hashCode() == b.hashCode());
    assertTrue(a.hashCode() != c.hashCode());
    assertTrue(a.hashCode() != d.hashCode());
    assertTrue(a.hashCode() != e.hashCode());
    assertTrue(a.hashCode() != f.hashCode());
    assertTrue(a.hashCode() != g.hashCode());
  }

  @Test
  public void testModuloComparison() {
    IntegerExpression a = new Modulo(new IValue(3), new IVar(2));
    IntegerExpression b = new Modulo(new IValue(3), new IVar(2));
    IntegerExpression c = new Modulo(new IValue(2), new IVar(3));
    IntegerExpression d = new Modulo(new IValue(3), new IVar(1));
    IntegerExpression e = new Modulo(new IValue(4), new IVar(2));
    IntegerExpression f = new Modulo(new IValue(-3), new IVar(2));
    assertTrue(a.compareTo(b) == 0);
    assertTrue(a.compareTo(c) < 0);
    assertTrue(a.compareTo(d) > 0);
    assertTrue(a.compareTo(e) < 0);
    assertTrue(a.compareTo(f) > 0);
  }

  @Test
  public void testModuloHashCode() {
    IntegerExpression a = new Modulo(new IValue(3), new IVar(2));
    IntegerExpression b = new Modulo(new IValue(3), new IVar(2));
    IntegerExpression c = new Modulo(new IValue(2), new IVar(3));
    IntegerExpression d = new Modulo(new IValue(3), new IVar(1));
    IntegerExpression e = new Modulo(new IValue(4), new IVar(2));
    IntegerExpression f = new Modulo(new IValue(-3), new IVar(2));
    assertTrue(a.hashCode() == b.hashCode());
    assertTrue(a.hashCode() != c.hashCode());
    assertTrue(a.hashCode() != d.hashCode());
    assertTrue(a.hashCode() != e.hashCode());
    assertTrue(a.hashCode() != f.hashCode());
  }

  private IntegerExpression make(IntegerExpression d, IntegerExpression n, boolean div) {
    if (div) return new Division(d, n);
    else return new Modulo(d, n);
  }

  @Test
  public void testQuerySimplified() {
    IntegerExpression x = new IVar(1);
    IntegerExpression y = new IVar(2);

    for (int i = 0; i < 2; i++) {
      boolean div = i == 0;

      IntegerExpression e = make(new Addition(x, y), new CMult(3, y), div);
      assertTrue(e.isSimplified());
      
      e = make(new Addition(x, x), y, div);
      assertFalse(e.isSimplified());

      e = make(x, new Addition(y, y), div);
      assertFalse(e.isSimplified());

      e = make(x, new IValue(1), div);
      assertFalse(e.isSimplified());

      e = make(x, new IValue(0), div);
      assertTrue(e.isSimplified());

      e = make(x, new IValue(-1), div);
      assertFalse(e.isSimplified());

      e = make(x, new CMult(-2, y), div);
      assertFalse(e.isSimplified());

      e = make(new IValue(8), new IValue(5), div);
      assertFalse(e.isSimplified());
    }
  }

  @Test
  public void testSimplifyBasics() {
    IntegerExpression x = new IVar(1);
    IntegerExpression y = new IVar(2);
    IntegerExpression m = new IValue(-3);
    IntegerExpression o = new IValue(1);
    IntegerExpression e;

    e = new Division(m, y);
    assertTrue(e.isSimplified());
    assertTrue(e.simplify() == e);

    e = new Modulo(m, y);
    assertTrue(e.isSimplified());
    assertTrue(e.simplify() == e);

    e = new Division(x, new Division(y, o));
    assertTrue(e.simplify().equals(new Division(x, y)));

    e = new Modulo(x, new Division(y, o));
    assertTrue(e.simplify().equals(new Modulo(x, y)));

    e = new Division(new IValue(5), new IValue(-3));
    assertTrue(e.simplify().equals(new IValue(-1)));
    e = new Modulo(new IValue(5), new IValue(-3));
    assertTrue(e.simplify().equals(new IValue(2)));
  }

  @Test
  public void testSimplifyDivisionByOne() {
    IntegerExpression x = new IVar(1);
    IntegerExpression y = new IVar(2);
    IntegerExpression o = new IValue(1);
    IntegerExpression u = new IValue(-1);
    IntegerExpression e;
 
    e = new Division(x, o);
    assertTrue(e.simplify().equals(x));

    e = new Modulo(x, o);
    assertTrue(e.simplify().equals(new IValue(0)));

    e = new Division(new Addition(x, y), u);
    assertTrue(e.simplify().equals(new Addition(new CMult(-1, x),
                                                new CMult(-1, y))));

    e = new Modulo(new Addition(x, y), u);
    assertTrue(e.simplify().equals(new IValue(0)));
  }

  @Test
  public void simplifyNegative() {
    IntegerExpression x = new IVar(1);
    IntegerExpression y = new IVar(2);
    IntegerExpression k = new IValue(3);
    IntegerExpression m = new IValue(-3);
    IntegerExpression e;

    // a div -b = -(a div b) and a mod -b = a mod b:
    // -b * (- (a div b)) + (a mod b) = b * (a div b) + a mod b = a
    e = new Division(x, m);
    assertTrue(e.simplify().equals(new CMult(-1, new Division(x, k))));

    e = new Modulo(x, m);
    assertTrue(e.simplify().equals(new Modulo(x, k)));

    e = new Division(x, new CMult(2, y));
    IntegerExpression f = (new Division(x, new CMult(-2, y))).simplify();
    assertTrue(e.simplify() == e);
    assertTrue(f.isSimplified());
    assertTrue(f.equals(new CMult(-1, e)));

    e = new Modulo(x, new CMult(2, y));
    f = (new Modulo(x, new CMult(-2, y))).simplify();
    assertTrue(e.simplify() == e);
    assertTrue(f.isSimplified());
    assertTrue(f.equals(e));
  }
}
