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
    Comparison neqcomp = comp.negate();
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
  public void testComparison() {
    IntegerExpression exp1 = new Addition(new IValue(-1), new IVar(2));
    IntegerExpression exp2 = new IVar(12);
    List<Constraint> parts = List.of(new Is0(exp1),  new Is0(exp2),
                                     new Geq0(exp1), new Geq0(exp2),
                                     new Neq0(exp1), new Neq0(exp2));
    for (int i = 0; i < parts.size(); i++) {
      for (int j = i+1; j < parts.size(); j++) {
        int k = parts.get(i).compareTo(parts.get(j));
        assertTrue(k != 0);
        assertTrue(k == - parts.get(j).compareTo(parts.get(i)));
      }
    }
    assertTrue(parts.get(0).equals(new Is0(exp1)));
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
}
