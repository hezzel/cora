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
  public void testEquality() {
    Constraint comp = SmtFactory.createSmaller(new IVar(2), new IValue(2));
    assertTrue(comp.equals(SmtFactory.createGreater(new IValue(2), new IVar(2))));
    assertFalse(comp.equals(SmtFactory.createGreater(new IVar(2), new IValue(2))));
    Constraint comp2 = SmtFactory.createGeq(new IValue(2), new IVar(2));
    assertFalse(comp.equals(comp2));
    assertFalse(comp2.equals(comp));
    Constraint comp3 = SmtFactory.createLeq(new IVar(2), new IValue(1));
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
