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

public class ComparisonTest {
  @Test
  public void testGreaterBasics() {
    IntegerExpression left = new Addition(new IValue(3), new IVar(7));
    IntegerExpression right = new IVar(4);
    Comparison comp = new Greater(left, right);
    assertTrue(comp.queryLeft().equals(left));
    assertTrue(comp.queryRight().equals(right));
    assertTrue(comp.toString().equals("(> (+ 3 i7) i4)"));
    assertTrue(SmtFactory.createSmaller(left, right).toString().equals("(> i4 (+ 3 i7))"));
  }

  @Test
  public void testGeqBasics() {
    IntegerExpression left = new Addition(new IValue(3), new IVar(7));
    IntegerExpression right = new IVar(4);
    Comparison comp = new Geq(left, right);
    assertTrue(comp.queryLeft().equals(left));
    assertTrue(comp.queryRight().equals(right));
    assertTrue(comp.toString().equals("(>= (+ 3 i7) i4)"));
    assertTrue(SmtFactory.createLeq(left, right).toString().equals("(>= i4 (+ 3 i7))"));
  }

  @Test
  public void testEquality() {
    Constraint comp = SmtFactory.createSmaller(new IVar(2), new IValue(2));
    assertTrue(comp.equals(SmtFactory.createGreater(new IValue(2), new IVar(2))));
    assertFalse(comp.equals(SmtFactory.createGreater(new IVar(2), new IValue(2))));
    Constraint comp2 = SmtFactory.createGeq(new IValue(2), new IVar(2));
    assertFalse(comp.equals(comp2));
    assertFalse(comp2.equals(comp));
  }

  @Test
  public void testLegalEvaluate() {
    IntegerExpression plus = new Addition(new IValue(3), new Addition(new IValue(12), new IValue(-2)));
    Constraint comp = SmtFactory.createGreater(plus, new IValue(12));
    comp = SmtFactory.createGreater(plus, new IValue(13));
    assertFalse(comp.evaluate());
    comp = SmtFactory.createGeq(plus, new IValue(13));
    assertTrue(comp.evaluate());
    comp = SmtFactory.createGeq(new IValue(12), plus);
    assertFalse(comp.evaluate());
  }
}
