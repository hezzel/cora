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
import java.util.List;
import charlie.util.Pair;

public class AdditionTest {
  @Test
  public void testStaggeredCreation() {
    Addition plus = new Addition(new IValue(3), new Addition(new IVar(12), new IValue(-2)));
    assertTrue(plus.numChildren() == 3);
    assertTrue(plus.queryChild(1).equals(new IValue(3)));
    assertTrue(plus.queryChild(2).equals(new IVar(12)));
    assertTrue(plus.queryChild(3).equals(new IValue(-2)));
  }

  @Test
  public void testMultiply() {
    IVar x = new IVar(3);
    IVar y = new IVar(5);
    IntegerExpression xy = new Multiplication(x, y);
    Addition plus = new Addition(new IValue(2), new Addition(x, new CMult(3, xy)));
    assertTrue(plus.multiply(0).equals(new IValue(0)));
    assertTrue(plus.multiply(1).equals(plus));
    assertTrue(plus.multiply(5).equals(
      new Addition(new IValue(10), new Addition(new CMult(5, x),
      new CMult(15, xy)))));
    assertTrue(plus.negate().equals(
      new Addition(new IValue(-2), new Addition(new CMult(-1, x),
      new CMult(-3, xy)))));
  }

  @Test
  public void testAdd() {
    IVar x = new IVar(3);
    IVar y = new IVar(2);
    Addition xy = new Addition(x, y);
    assertTrue(xy.add(0).equals(xy));
    assertTrue(xy.add(-4).equals(new Addition(new IValue(-4), xy)));
    Addition oyx = new Addition(new IValue(1), new Addition(y, x));
    assertTrue(oyx.add(5).equals(new Addition(List.of(new IValue(6), y, x))));
    assertTrue(oyx.add(-2).isSimplified());
    assertTrue(oyx.add(-1).isSimplified());
    assertTrue(oyx.add(-1).equals(new Addition(y, x)));
  }

  @Test
  public void testSplit() {
    IVar x = new IVar(1);
    IVar y = new IVar(2);
    Addition a = new Addition(List.of(x, new IValue(3), new CMult(-1, y), new CMult(2, x),
      new CMult(-7, x), new CMult(-3, new Multiplication(x, y)), new IValue(-4)));
    Pair<IntegerExpression,IntegerExpression> p = a.split();
    assertTrue(p.fst().equals(new Addition(List.of(x, new CMult(2, x)))));
    assertTrue(p.snd().equals(new Addition(List.of(new IValue(1), y, new CMult(7, x),
      new CMult(3, new Multiplication(x, y))))));
  }

  @Test
  public void testEquality() {
    IntegerExpression plus = new Addition(new IValue(1), new IValue(2));
    IntegerExpression plus2 = new Addition(new IValue(1), new IValue(2));
    assertTrue(plus.equals(new Addition(new IValue(1), new IValue(2))));
    assertTrue(plus.hashCode() == plus2.hashCode());
    IntegerExpression mult = new Multiplication(new IValue(1), new IValue(2));
    assertFalse(plus.equals(mult));
    assertTrue(plus.hashCode() != mult.hashCode());
    assertFalse(plus.equals(new IValue(3)));
  }

  @Test
  public void testComparison() {
    IntegerExpression x = new IVar(1);
    IntegerExpression u = new IVar(2);
    IntegerExpression y = new IVar(3);
    IntegerExpression z = new IVar(4);
    IntegerExpression o = new IValue(1);
    IntegerExpression a = new Addition(o, new Addition(x, y)); // 1 + x + y
    IntegerExpression b = new Addition(x, y);                  // x + y
    assertTrue(a.compareTo(b) > 0);
    assertTrue(b.compareTo(a) < 0);
    assertTrue(a.compareTo(z) > 0);
    assertTrue(a.compareTo(new Addition(x,z)) < 0);
    assertTrue(a.compareTo(new Addition(y, new Addition(x, new IValue(1)))) != 0);
  }

  @Test
  public void testToString() {
    IntegerExpression plus = new Addition(List.of(new IValue(-3), new IValue(7), new IVar(0)));
    assertTrue(plus.toSmtString().equals("(+ (- 3) 7 i0)"));
    assertTrue(plus.toString().equals("-3 + 7 + i0"));
  }

  @Test
  public void testLegalEvaluate() {
    IntegerExpression plus =
      new Addition(new IValue(3), new Addition(new IValue(12), new IValue(-2)));
    assertTrue(plus.evaluate() == 13);
  }

  @Test
  public void testQueryBadChild() {
    Addition plus = new Addition(new IValue(0), new IVar(2));
    assertThrows(charlie.exceptions.IndexingException.class, () -> plus.queryChild(0));
    assertThrows(charlie.exceptions.IndexingException.class, () -> plus.queryChild(3));
  }

  @Test
  public void testSimplified() {
    IntegerExpression x = new IVar(1);
    IntegerExpression y = new IVar(2);
    IntegerExpression k = new IValue(3);
    IntegerExpression a;

    a = new Addition(List.of(k, x, y));
    assertTrue(a.isSimplified());
    a = new Addition(List.of(x, k, y));
    assertFalse(a.isSimplified());
    a = new Addition(List.of(k, new CMult(-4, x), y));
    assertTrue(a.isSimplified());
    a = new Addition(List.of(x, x, y));
    assertFalse(a.isSimplified());
    a = new Addition(x, new Multiplication(k, y));
    assertFalse(a.isSimplified());
    a = new Addition(List.of(k, new IValue(7), x));
    assertFalse(a.isSimplified());
    a = new Addition(List.of(x, y, new CMult(3, y)));
    assertFalse(a.isSimplified());
    a = new Addition(new CMult(-2, y), new CMult(3, y));
    assertFalse(a.isSimplified());
    a = new Addition(List.of(x));
    assertFalse(a.isSimplified());
  }

  @Test
  public void testSimplify() {
    IntegerExpression x = new IVar(1);
    IntegerExpression y = new IVar(2);
    IntegerExpression one = new IValue(1);
    IntegerExpression two = new IValue(2);
    IntegerExpression three = new IValue(3);
    IntegerExpression xy = new Multiplication(x, y);
    IntegerExpression a, s;

    a = new Addition(one, two);
    assertTrue(a.simplify().equals(three));

    a = new Addition(y, x);
    assertTrue(a.simplify().equals(new Addition(x, y)));

    a = new Addition(List.of(x, y, x));
    assertTrue(a.simplify().equals(new Addition(new CMult(2, x), y)));

    a = new Addition(List.of(new CMult(3, x), y, new CMult(2, x), new CMult(-1, y)));
    assertTrue(a.simplify().equals(new CMult(5, x)));

    a = new Addition(List.of(new CMult(2, xy), x, new CMult(-1, xy), new CMult(-3, x)));
    s = a.simplify();
    assertTrue(s.isSimplified());
    assertTrue(s.equals(new Addition(new CMult(-2, x), xy)));

    a = new Addition(x, new CMult(-1, x));
    assertTrue(a.simplify().equals(new IValue(0)));

    a = new Addition(List.of(x, new CMult(3, new Addition(x, one)), new IValue(-4)));
    assertTrue(a.simplify().equals(new Addition(new IValue(-1), new CMult(4, x))));
  }
}
