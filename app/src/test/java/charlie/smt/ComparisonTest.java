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

public class ComparisonTest {
  @Test
  public void testGreaterBasics() {
    IntegerExpression left = new Addition(new IValue(3), new IVar(7));
    IntegerExpression right = new IVar(4);
    Comparison comp = (Comparison)SmtFactory.createGreater(left, right);
    assertTrue(comp.queryExpression().equals(new Addition(List.of(
      new IValue(3), new IVar(7), new IValue(-1), new CMult(-1, new IVar(4))))));
    assertTrue(SmtFactory.createSmaller(right, left).equals(comp));
    assertTrue(comp.negate().negate().equals(comp));
    assertTrue(comp.negate().equals(new Geq0(new Addition(List.of(
      new IValue(-4), new CMult(-1, new IVar(7)), new IValue(1), new IVar(4))))));
  }

  @Test
  public void testGeqBasics() {
    IntegerExpression left = new Addition(new IValue(3), new IVar(7));
    IntegerExpression right = new IVar(4);
    Comparison comp = (Comparison)SmtFactory.createGeq(left, right);
    assertTrue(comp.queryExpression().toString().equals("3 + i7 + -i4"));
    assertTrue(comp.toString().equals("3 + i7 >= i4"));
    assertTrue(SmtFactory.createLeq(left, right).toString().equals("i4 >= 3 + i7"));
  }

  @Test
  public void testEqualUnequalBasics() {
    IntegerExpression expr = new Addition(new IValue(-1), new IVar(2));
    Comparison comp = (Comparison)SmtFactory.createEqual(expr);
    Constraint neqcomp = comp.negate();
    assertTrue(neqcomp.equals(SmtFactory.createUnequal(expr)));
    assertTrue(neqcomp.hashCode() == SmtFactory.createUnequal(expr).hashCode());
    assertTrue(neqcomp.hashCode() == comp.hashCode() + 1);
    assertTrue(neqcomp.negate().equals(comp));
    assertTrue(comp.toString().equals("i2 = 1"));
    assertTrue(neqcomp.toString().equals("i2 # 1"));
    assertTrue(comp.toSmtString().equals("(= (+ (- 1) i2) 0)"));
    assertTrue(neqcomp.toSmtString().equals("(distinct (+ (- 1) i2) 0)"));
  }

  @Test
  public void testCompareToSameExpression() {
    IntegerExpression exp = new Addition(new IValue(-1), new IVar(2));
    List<Constraint> parts = List.of(new Is0(exp), new Geq0(exp), new Neq0(exp));
    for (int i = 0; i < parts.size(); i++) {
      for (int j = 0; j < parts.size(); j++) {
        if (j < i) assertTrue(parts.get(i).compareTo(parts.get(j)) == 1);
        if (j == i) assertTrue(parts.get(i).compareTo(parts.get(j)) == 0);
        if (j > i) assertTrue(parts.get(i).compareTo(parts.get(j)) == -1);
      }
    }
  }

  @Test
  public void testCompareToDifferentExpressions() {
    IntegerExpression exp1 = new IVar(1);
    IntegerExpression exp2 = new IVar(2);
    
    List<Constraint> p1 = List.of(new Is0(exp1), new Geq0(exp1), new Neq0(exp1));
    List<Constraint> p2 = List.of(new Is0(exp2), new Geq0(exp2), new Neq0(exp2));
    
    for (int i = 0; i < p1.size(); i++) {
      for (int j = 0; j < p2.size(); j++) {
        assertTrue(p1.get(i).compareTo(p2.get(j)) <= -2);
        assertTrue(p2.get(i).compareTo(p1.get(j)) >= 2);
      }
    }
  }

  @Test
  public void testEquality() {
    Constraint comp = SmtFactory.createSmaller(new IVar(2), new IValue(2));
    Constraint comp2 = SmtFactory.createGreater(new IValue(2), new IVar(2));
    assertTrue(comp.equals(comp2));
    assertTrue(comp.hashCode() == comp2.hashCode());
    Constraint comp3 = SmtFactory.createGreater(new IVar(2), new IValue(2));
    assertFalse(comp.equals(comp3));
    assertTrue(comp.hashCode() != comp3.hashCode());
    Constraint comp4 = SmtFactory.createGeq(new IValue(2), new IVar(2));
    assertFalse(comp.equals(comp4));
    assertFalse(comp4.equals(comp));
  }

  @Test
  public void testLegalEvaluate() {
    IntegerExpression plus = new Addition(new IValue(3), new Addition(new IValue(12), new IValue(-2)));
    Constraint comp1, comp2, comp3;

    comp1 = SmtFactory.createEqual(plus, new IValue(13));
    comp2 = SmtFactory.createUnequal(plus, new IValue(13));
    comp3 = SmtFactory.createGeq(plus, new IValue(13));
    assertTrue(comp1.evaluate());
    assertFalse(comp2.evaluate());
    assertTrue(comp3.evaluate());
    comp1 = SmtFactory.createEqual(plus, new IValue(14));
    comp2 = SmtFactory.createUnequal(plus, new IValue(14));
    comp3 = SmtFactory.createGeq(plus, new IValue(14));
    assertFalse(comp1.evaluate());
    assertTrue(comp2.evaluate());
    assertFalse(comp3.evaluate());
    comp3 = SmtFactory.createGeq(plus, new IValue(12));
    assertTrue(comp3.evaluate());
  }

  @Test
  public void testBasicSimplify() {
    // 1 + x - 2 x ≥ 0 -- the subexpression should be simplified
    IVar x = new IVar(3, "x");
    IntegerExpression expr = new Addition(new IValue(1), new Addition(x, new CMult(-2, x)));
    Constraint comparison = new Geq0(expr);
    assertFalse(comparison.isSimplified());
    assertTrue(comparison.simplify().isSimplified());
    assertTrue(comparison.simplify().toString().equals("1 >= [x]"));

    // 3 ≥ 0 -- this can be evaluated to true
    IValue v = new IValue(3);
    comparison = new Is0(v);
    assertFalse(comparison.isSimplified());
    assertTrue(comparison.simplify().equals(new Falsehood()));
    comparison = new Geq0(v);
    assertFalse(comparison.isSimplified());
    assertTrue(comparison.simplify().equals(new Truth()));

    // 0 * x # 0 -- this can be evaluated to false
    comparison = new Neq0(new CMult(0, x));
    assertFalse(comparison.isSimplified());
    assertTrue(comparison.simplify().equals(new Falsehood()));
  }

  @Test
  public void testCMultSimplify() {
    // 7x = 0, 7x # 0, 7x ≥ 0; this can all be simplified by dividing out the 7
    IVar x = new IVar(7, "x");
    IntegerExpression expr = new CMult(3, x);
    Constraint c1 = new Is0(expr);
    Constraint c2 = new Neq0(expr);
    Constraint c3 = new Geq0(expr);
    assertFalse(c1.isSimplified());
    assertFalse(c2.isSimplified());
    assertFalse(c3.isSimplified());
    assertTrue(c1.simplify().toString().equals("[x] = 0"));
    assertTrue(c2.simplify().toString().equals("[x] # 0"));
    assertTrue(c3.simplify().toString().equals("[x] >= 0"));

    // -7x = 0, -7x # 0, -7x ≥ 0; for the first two we can divide out the 7, but for the last we
    // need to keep -1 there
    expr = new CMult(-7, x);
    c1 = new Is0(expr); c2 = new Neq0(expr); c3 = new Geq0(expr);
    assertFalse(c1.isSimplified());
    assertFalse(c2.isSimplified());
    assertFalse(c3.isSimplified());
    assertTrue(c1.simplify().toString().equals("[x] = 0"));
    assertTrue(c2.simplify().toString().equals("[x] # 0"));
    assertTrue(c3.simplify().toString().equals("-[x] >= 0"));
    assertTrue(c1.simplify().isSimplified());
    assertTrue(c2.simplify().isSimplified());
    assertTrue(c3.simplify().isSimplified());

    // -3 * (x - 11); this is similarly simplified, even though the CMult disappears after the
    // simplification of the subexpression
    expr = new CMult(-3, x.add(-11));
    c1 = new Is0(expr); c2 = new Neq0(expr); c3 = new Geq0(expr);
    assertFalse(c1.isSimplified());
    assertFalse(c2.isSimplified());
    assertFalse(c3.isSimplified());
    assertTrue(c1.simplify().toString().equals("[x] = 11"));
    assertTrue(c2.simplify().toString().equals("[x] # 11"));
    assertTrue(c3.simplify().toString().equals("11 >= [x]"));
    assertTrue(c3.simplify().isSimplified());
  }

  @Test
  public void testMultiplicationSimplify() {
    IVar x = new IVar(3, "x");
    IVar y = new IVar(12, "y");

    // x * y R 0 -- so the multiplication is already in simplified form
    IntegerExpression xy = new Multiplication(x, y);
    Constraint c1 = new Is0(xy);
    Constraint c2 = new Neq0(xy);
    Constraint c3 = new Geq0(xy);
    assertFalse(c1.isSimplified());
    assertFalse(c2.isSimplified());
    assertTrue(c3.isSimplified());
    assertTrue(c1.simplify().toString().equals("([x] = 0) or ([y] = 0)"));
    assertTrue(c2.simplify().toString().equals("([x] # 0) and ([y] # 0)"));
    assertTrue(c3.simplify().toString().equals("[x] * [y] >= 0"));

    // 0 + x * 2 * y R 0 -- so the multiplication only appears after simplifying, and within a CMult
    IntegerExpression expr = new Addition(new IValue(0), new Multiplication(x, new CMult(2, y)));
    c1 = new Is0(expr);
    c2 = new Neq0(expr);
    c3 = new Geq0(expr);
    assertTrue(c1.simplify().toString().equals("([x] = 0) or ([y] = 0)"));
    assertTrue(c2.simplify().toString().equals("([x] # 0) and ([y] # 0)"));
    assertTrue(c3.simplify().toString().equals("[x] * [y] >= 0"));

    // (x + 1) * (x - 1) R 0 -- so the multiplication DISAPPEARS after simplifying
    expr = new Multiplication(x.add(1), x.add(-1));
    c1 = new Is0(expr);
    c2 = new Neq0(expr);
    c3 = new Geq0(expr);
    assertTrue(c1.simplify().toString().equals("([x] = 1) or (1 + [x] = 0)"));
    assertTrue(c2.simplify().toString().equals("([x] # 1) and (1 + [x] # 0)"));
    assertTrue(c3.simplify().toString().equals("[x] * [x] >= 1"));
  }

  @Test
  public void testNegativeLargest() {
    IVar x = new IVar(3, "x");
    IVar z = new IVar(1, "z");
    IntegerExpression neg = new CMult(-3, x);

    // z + x R 0 -- this is simplified no matter what
    IntegerExpression expr1 = new Addition(z, x);
    assertTrue((new Is0(expr1)).isSimplified());
    assertTrue((new Neq0(expr1)).isSimplified());
    assertTrue((new Geq0(expr1)).isSimplified());

    // z - 3 * x R 0 -- this is not simplified for = or #, since we want to negate such expressions
    // to make the highest component positive
    IntegerExpression expr2 = new Addition(z, neg);
    Constraint c1 = new Is0(expr2);
    Constraint c2 = new Neq0(expr2);
    Constraint c3 = new Geq0(expr2);
    assertFalse(c1.isSimplified());
    assertTrue(c1.simplify().toString().equals("3 * [x] = [z]"));
    assertFalse(c2.isSimplified());
    assertTrue(c2.simplify().toString().equals("3 * [x] # [z]"));
    assertTrue(c3.isSimplified());
    assertTrue(c3.simplify() == c3);

    // z - 3 * x + x * y = 0 -- this is implified again, because x * y is the highest component and
    // is positive
    IntegerExpression expr3 = new Addition(expr2, new Multiplication(x, new IVar(4, "y")));
    assertTrue((new Is0(expr3)).isSimplified());
  }

  @Test
  public void testCMultAdditionSimplify() {
    IValue two = new IValue(2);
    IVar x = new IVar(7 ,"x");
    IVar y = new IVar(13, "y");

    // 2 + x + 3 x y = 0 is simplified, because it has more than 2 arguments
    Addition a = new Addition(two, new Addition(x, new CMult(3, new Multiplication(x, y))));
    Constraint c = new Is0(a);
    assertTrue(c.isSimplified());

    // 2 + x # 0 is simplified
    c = new Neq0(new Addition(two, x));
    assertTrue(c.isSimplified());

    // 2 + 1 * x = 0 simplifies to 2 + x = 0
    c = new Is0(new Addition(two, new CMult(1, x)));
    assertFalse(c.isSimplified());
    c = c.simplify();
    assertTrue(c.isSimplified());
    assertTrue(c.equals(new Is0(new Addition(two, x))));

    // 2 + 3 x y
    a = new Addition(two, new CMult(3, new Multiplication(x, y)));
    assertTrue((new Is0(a)).simplify().equals(new Falsehood()));
    assertTrue((new Neq0(a)).simplify().equals(new Truth()));

    // 6 + 2 x
    a = new Addition(new IValue(6), new CMult(2, x));
    assertTrue((new Is0(a)).simplify().toString().equals("3 + [x] = 0"));
    assertTrue((new Neq0(a)).simplify().toString().equals("3 + [x] # 0"));
    
    // 16 + 12 x
    a = new Addition(new IValue(16), new CMult(12, x));
    assertTrue((new Is0(a)).simplify().equals(new Falsehood()));
    assertTrue((new Neq0(a)).simplify().equals(new Truth()));
  }

  private void checkGeq(IntegerExpression expr, String goal) {
    Constraint c = new Geq0(expr);
    Constraint d = c.simplify();
    assertTrue(d.isSimplified(), "Simplifying " + c + " gives something unsimplified");
    assertTrue(d.toString().equals(goal), "Simplifying " + c + " does not give " + goal +
                                          " but rather " + d);
  }

  @Test
  public void testCMultAdditionSimplifyGeq() {
    IValue two = new IValue(2);
    IValue six = new IValue(6);
    IValue seven = new IValue(7);
    IValue mtwo = new IValue(-2);
    IValue msix = new IValue(-6);
    IValue mseven = new IValue(-7);
    IVar x = new IVar(7 ,"x");
    IVar y = new IVar(13, "y");

    // 2 + x + 3 x y ≥ 0 is simplified, because it has more than 2 arguments
    Addition a = new Addition(two, new Addition(x, new CMult(3, new Multiplication(x, y))));
    assertTrue((new Geq0(a)).isSimplified());

    // 2 - x ≥ 0 is simplified
    assertTrue((new Geq0(new Addition(two, new CMult(-1, x)))).isSimplified());

    // 2 + 1 * x ≥ 0 simplifies to 2 + x = 0
    checkGeq(new Addition(two, new CMult(1, x)), "2 + [x] >= 0");

    // 2 + 3 x ≥ 0 -- that is, 3 x ≥ -2, becomes x ≥ CEIL(-2/3) = 0
    checkGeq(new Addition(two, new CMult(3, x)), "[x] >= 0");
    // 6 + 3 x ≥ 0 -- that is, 2 + [x] ≥ 0
    checkGeq(new Addition(six, new CMult(3, x)), "2 + [x] >= 0");
    // 7 + 3 x ≥ 0 -- that is, 3 x ≥ -7, becomes x ≥ CEIL(-7/3) = -2
    checkGeq(new Addition(seven, new CMult(3, x)), "2 + [x] >= 0");

    // -2 + 3 x ≥ 0 -- that is, 3 x ≥ 2, becomes x ≥ CEIL(2/3) = 1
    checkGeq(new Addition(mtwo, new CMult(3, x)), "[x] >= 1");
    // -6 + 3 x ≥ 0 -- that is, 3 x ≥ 6, becomes x ≥ CEIL(6/3) = 2
    checkGeq(new Addition(msix, new CMult(3, x)), "[x] >= 2");
    // -7 + 3 x ≥ 0 -- that is, 3 x ≥ 7, becomes x ≥ CEIL(7/3) = 3
    checkGeq(new Addition(mseven, new CMult(3, x)), "[x] >= 3");

    // 2 - 3 x ≥ 0 -- that is, 2 ≥ 3 x, becomes 2/3 ≥ x, so x ≤ FLOOR(2/3) = 0
    checkGeq(new Addition(two, new CMult(-3, x)), "-[x] >= 0");
    // 6 - 3 x ≥ 0 -- that is, 6 ≥ 3 x, so 2 ≥ x
    checkGeq(new Addition(six, new CMult(-3, x)), "2 >= [x]");
    // 7 - 3 x ≥ 0 -- that is, 7 ≥ 3 x, so FLOOR(7/3) ≥ x
    checkGeq(new Addition(seven, new CMult(-3, x)), "2 >= [x]");

    // -2 - 3 x ≥ 0 -- that is, -2 ≥ 3 x, becomes x ≤ FLOOR(-2/3) = -1
    checkGeq(new Addition(mtwo, new CMult(-3, x)), "0 >= 1 + [x]");
    // -6 - 3 x ≥ 0 -- that is, -6 ≥ 3 x, becomes x ≤ -2
    checkGeq(new Addition(msix, new CMult(-3, x)), "0 >= 2 + [x]");
    // -7 - 3 x ≥ 0 -- that is, -7 ≥ 3 x, becomes x ≤ FLOOR(-7/3) = -3
    checkGeq(new Addition(mseven, new CMult(-3, x)), "0 >= 3 + [x]");
  }
}

