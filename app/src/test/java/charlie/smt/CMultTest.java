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

package charlie.smt;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class CMultTest {
  @Test
  public void testBasics() {
    CMult cm =
      new CMult(-1, new Addition(new IValue(-4), new IVar(1)));
    assertTrue(cm.queryChild().equals(new Addition(new IValue(-4), new IVar(1))));
    assertTrue(cm.toSmtString().equals("(- (+ (- 4) i1))"));
    assertTrue(cm.toString().equals("-(-4 + i1)"));
  }

  @Test
  public void testLegalEvaluate() {
    IntegerExpression minus =
      new CMult(-2,
      new CMult(1,
      new CMult(3,
      new Multiplication(new IValue(3), new IValue(-5)))));
    assertTrue(minus.evaluate() == 90);
  }

  @Test
  public void testMultiply() {
    IVar x = new IVar(2);
    IntegerExpression cm = new CMult(-1, x);
    assertTrue(cm.multiply(0).equals(new IValue(0)));
    assertTrue(cm.multiply(1).equals(cm));
    assertTrue(cm.multiply(-1).equals(x));
    assertTrue(cm.multiply(2).equals(new CMult(-2, x)));
    assertTrue(cm.multiply(-2).equals(new CMult(2, x)));
    assertTrue(cm.negate().equals(x));
  }

  @Test
  public void testToString() {
    IntegerExpression xy = new Multiplication(new IVar(1), new IVar(2));
    CMult a = new CMult(-2, xy);
    CMult b = new CMult(-1, xy);
    CMult c = new CMult(0, xy);
    CMult d = new CMult(1, xy);
    CMult e = new CMult(2, xy);
    assertTrue(a.toString().equals("-2 * i1 * i2"));
    assertTrue(b.toString().equals("-(i1 * i2)"));
    assertTrue(c.toString().equals("0 * i1 * i2"));
    assertTrue(d.toString().equals("1 * i1 * i2"));
    assertTrue(e.toString().equals("2 * i1 * i2"));
  }

  @Test
  public void testToSmtString() {
    IntegerExpression xy = new Multiplication(new IVar(1), new IVar(2));
    CMult a = new CMult(-2, xy);
    CMult b = new CMult(-1, xy);
    CMult c = new CMult(0, xy);
    CMult d = new CMult(1, xy);
    CMult e = new CMult(2, xy);
    assertTrue(a.toSmtString().equals("(* (- 2) (* i1 i2))"));
    assertTrue(b.toSmtString().equals("(- (* i1 i2))"));
    assertTrue(c.toSmtString().equals("(* 0 (* i1 i2))"));
    assertTrue(d.toSmtString().equals("(* 1 (* i1 i2))"));
    assertTrue(e.toSmtString().equals("(* 2 (* i1 i2))"));
  }

  @Test
  public void testComparison() {
    IntegerExpression mf = new IValue(-4);
    IntegerExpression mt = new IValue(-3);
    IntegerExpression x = new IVar(1);
    IntegerExpression m1 = new CMult(-2, new Addition(mf, x));
    IntegerExpression m2 = new CMult(-2, new Addition(mf, x));
    IntegerExpression m3 = new CMult(-2, new Addition(mt, x));
    IntegerExpression m4 = new Multiplication(new IValue(-2), new Addition(mf, x));
    IntegerExpression p = new Addition(new IValue(8), new CMult(-2, x));
    assertTrue(m1.compareTo(m2) == 0);
    assertTrue(m1.compareTo(m3) < 0);
    assertTrue(m1.compareTo(m4) != 0);
    assertTrue(m1.compareTo(m4) == -m4.compareTo(m1));
    assertTrue(m1.compareTo(p) != 0);
    assertTrue(m1.compareTo(p) == -p.compareTo(m1));
  }

  @Test
  public void testHashCode() {
    IntegerExpression mf = new IValue(-4);
    IntegerExpression mt = new IValue(-3);
    IntegerExpression x = new IVar(1);
    IntegerExpression m1 = new CMult(-2, new Addition(mf, x));
    IntegerExpression m2 = new CMult(-2, new Addition(mf, x));
    IntegerExpression m3 = new CMult(-2, new Addition(mt, x));
    IntegerExpression m4 = new Multiplication(new IValue(-2), new Addition(mf, x));
    IntegerExpression p = new Addition(new IValue(8), new CMult(-2, x));
    assertTrue(m1.hashCode() == m2.hashCode());
    assertTrue(m1.hashCode() != m3.hashCode());
    assertTrue(m1.hashCode() != m4.hashCode());
    assertTrue(m1.hashCode() != p.hashCode());
  }

  @Test
  public void testSimplified() {
    IntegerExpression x = new IVar(1);
    IntegerExpression y = new IVar(2);
    IntegerExpression k = new IValue(3);

    IntegerExpression ie = new CMult(0, x);
    assertFalse(ie.isSimplified());

    ie = new CMult(1, x);
    assertFalse(ie.isSimplified());

    ie = new CMult(2, x);
    assertTrue(ie.isSimplified());

    ie = new CMult(-1, x);
    assertTrue(ie.isSimplified());

    ie = new CMult(3, k);
    assertFalse(ie.isSimplified());

    ie = new CMult(3, new CMult(2, x));
    assertFalse(ie.isSimplified());

    ie = new CMult(3, new Addition(x, y));
    assertFalse(ie.isSimplified());

    ie = new CMult(3, new Division(x, y));
    assertTrue(ie.isSimplified());

    ie = new CMult(2, new Multiplication(y, x));
    assertFalse(ie.isSimplified());
  }

  @Test
  public void testSimplify() {
    IntegerExpression x = new IVar(1);
    IntegerExpression y = new IVar(2);

    IntegerExpression ie = new CMult(0, x);
    IntegerExpression is = ie.simplify();
    assertTrue(is.equals(new IValue(0)));

    ie = new CMult(1, x); is = ie.simplify();
    assertTrue(is == x);

    ie = new CMult(2, new CMult(3, new IValue(1)));
    is = ie.simplify();
    assertTrue(is.equals(new IValue(6)));

    ie = new CMult(2, new Division(new IValue(9), new IValue(2)));
    is = ie.simplify();
    assertTrue(is.equals(new IValue(8)));

    ie = new CMult(2, x); is = ie.simplify();
    assertTrue(is == ie);

    ie = new CMult(2, new CMult(1, x)); is = ie.simplify();
    assertTrue(is.equals(new CMult(2, x)));
    assertTrue(is.isSimplified());

    ie = new CMult(-3, new CMult(4, x)); is = ie.simplify();
    assertTrue(is.equals(new CMult(-12, x)));
    assertTrue(is.isSimplified());

    ie = new CMult(-1, new CMult(-1, x)); is = ie.simplify();
    assertTrue(is == x);
    assertTrue(is.isSimplified());

    ie = new CMult(4, new Addition(x, y)); is = ie.simplify();
    assertTrue(is.equals(new Addition(new CMult(4, x),
                                      new CMult(4, y))));
    
    ie = new CMult(-5, new Multiplication(x, y)); is = ie.simplify();
    assertTrue(is == ie);

    ie = new CMult(2, new Division(x, new Addition(new IValue(2), new IValue(2))));
    is = ie.simplify();
    assertTrue(is.equals(new CMult(2, new Division(x, new IValue(4)))));
    assertTrue(is.isSimplified());

    ie = new CMult(2, new Modulo(x, y)); is = ie.simplify();
    assertTrue(is == ie);
  }
}
