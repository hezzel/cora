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

public class MultiplicationTest {
  @Test
  public void testStaggeredCreation() {
    IntegerExpression x = new IVar(13);
    IntegerExpression y = new IVar(12);
    Multiplication prod = new Multiplication(new IValue(3),
      new Multiplication(new Addition(x, y), new IValue(-2)));
    assertTrue(prod.numChildren() == 3);
    assertTrue(prod.queryChild(1).equals(new IValue(3)));
    assertTrue(prod.queryChild(2).equals(new Addition(x, y)));
    assertTrue(prod.queryChild(3).equals(new IValue(-2)));

    prod = new Multiplication(x, new CMult(3, y));
    assertTrue(prod.equals(new Multiplication(List.of(x, new IValue(3), y))));
  }

  @Test
  public void testToString() {
    IntegerExpression prod =
      new Multiplication(List.of(new IValue(-3), new IValue(7), new IVar(0)));
    assertTrue(prod.toSmtString().equals("(* (- 3) 7 i0)"));
    assertTrue(prod.toString().equals("-3 * 7 * i0"));
  }

  @Test
  public void testLegalEvaluate() {
    IntegerExpression prod =
      new Multiplication(new IValue(3), new Multiplication(new IValue(12), new IValue(-2)));
    assertTrue(prod.evaluate() == -72);
  }

  @Test
  public void testQueryBadChild() {
    Multiplication prod = new Multiplication(new IValue(0), new IVar(2));
    assertThrows(charlie.exceptions.IndexingException.class, () -> prod.queryChild(0));
    assertThrows(charlie.exceptions.IndexingException.class, () -> prod.queryChild(3));
  }

  @Test
  public void testComparison() {
    // a * b * c < b * d
    // b * c < a * b * c
    IntegerExpression a = new IVar(1);
    IntegerExpression b = new IVar(2);
    IntegerExpression c = new IVar(3);
    IntegerExpression d = new IVar(4);
    IntegerExpression abc = new Multiplication(a, new Multiplication(b, c));
    IntegerExpression bd = new Multiplication(b, d);
    IntegerExpression bc = new Multiplication(b, c);
    assertTrue(abc.compareTo(bd) < 0);
    assertTrue(bd.compareTo(abc) > 0);
    assertTrue(bc.compareTo(abc) < 0);
    assertTrue(abc.compareTo(bc) > 0);
    assertTrue(abc.compareTo(abc) == 0);
  }

  @Test
  public void testSimplified() {
    Multiplication m;
    IntegerExpression x = new IVar(1);
    IntegerExpression y = new IVar(2);
    IntegerExpression z = new IVar(3);

    m = new Multiplication(List.of(x, y, z));
    assertTrue(m.isSimplified());
    m = new Multiplication(List.of(x, new Division(y, z)));
    assertTrue(m.isSimplified());
    m = new Multiplication(List.of(x, new Addition(y, z)));
    assertFalse(m.isSimplified());
    m = new Multiplication(List.of(new IValue(3), y, z));
    assertFalse(m.isSimplified());
    m = new Multiplication(List.of(x, new CMult(2, z)));
    assertFalse(m.isSimplified());
    m = new Multiplication(List.of(x, z, y));
    assertFalse(m.isSimplified());
    m = new Multiplication(List.of(new Division(x, y), z));
    assertFalse(m.isSimplified());
    m = new Multiplication(List.of(x, x, y));
    assertTrue(m.isSimplified());
    m = new Multiplication(List.of(y));
    assertFalse(m.isSimplified());
  }

  @Test
  public void testSimplify() {
    Multiplication m;
    IntegerExpression x = new IVar(1);
    IntegerExpression y = new IVar(2);
    IntegerExpression z = new IVar(3);

    // x * y * z
    m = new Multiplication(List.of(x, y, z));
    assertTrue(m.simplify() == m);

    // z * y * x
    m = new Multiplication(List.of(z, y, x));
    assertTrue(m.simplify().equals(new Multiplication(List.of(x, y, z))));

    // x * 3
    m = new Multiplication(x, new IValue(3));
    assertTrue(m.simplify().equals(new CMult(3, x)));

    // 3 * 12
    m = new Multiplication(new IValue(3), new IValue(12));
    assertTrue(m.simplify().equals(new IValue(36)));

    // -1 * (y + x) * 2
    m = new Multiplication(List.of(new IValue(-1), new Addition(y, x), new IValue(2)));
    assertTrue(m.simplify().equals(new Addition(new CMult(-2, x), new CMult(-2, y))));

    // x * 3 * x
    m = new Multiplication(List.of(x, new IValue(3), x));
    assertTrue(m.simplify().equals(new CMult(3, new Multiplication(x, x))));

    // x * 2 * -6
    m = new Multiplication(List.of(x, new Modulo(new IValue(6), new IValue(4)), new IValue(-6)));
    assertTrue(m.simplify().equals(new CMult(-12, x)));

    // x * (3 * z * x) * y
    m = new Multiplication(List.of(x, new Multiplication(List.of(new IValue(3), z, x)), y));
    IntegerExpression s = m.simplify();
    assertTrue(s.equals(new CMult(3, new Multiplication(List.of(x, x, y, z)))));
    assertTrue(s.isSimplified());

    // y * (2 * xz - zx)
    m = new Multiplication(y, new Addition(new CMult(2, new Multiplication(x, z)),
      new Multiplication(z, x)));
    s = new Multiplication(List.of(x, y, z));
    assertTrue(s.isSimplified());

    // x * (y + z + 1)
    m = new Multiplication(x, new Addition(List.of(y, z, new IValue(1))));
    assertTrue(m.simplify().equals(new Addition(List.of(x, new Multiplication(x, y),
      new Multiplication(x, z)))));

    // (x + y) * (1 + x - y) ==> x + xx + y - yy
    m = new Multiplication(new Addition(x, y),
                            new Addition(List.of(new IValue(1), x, new CMult(-1, y))));
    assertTrue(m.simplify().equals(new Addition(List.of(x, y, new Multiplication(x,x),
      new CMult(-1, new Multiplication(y, y))))));
  }
}

