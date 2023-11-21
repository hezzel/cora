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

package cora.smt;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;

public class ComparisonTest {
  @Test
  public void testGreaterBasics() {
    IntegerExpression left = new Addition(new IValue(3), new IVar(7));
    IntegerExpression right = new IVar(4);
    Comparison comp = new Greater(left, right);
    assertTrue(comp.queryLeft().equals(left));
    assertTrue(comp.queryRight().equals(right));
    assertTrue(comp.toString().equals("(> (+ 3 i7) i4)"));
    assertTrue(SmtProblem.createSmaller(left, right).toString().equals("(> i4 (+ 3 i7))"));
  }

  @Test
  public void testGeqBasics() {
    IntegerExpression left = new Addition(new IValue(3), new IVar(7));
    IntegerExpression right = new IVar(4);
    Comparison comp = new Geq(left, right);
    assertTrue(comp.queryLeft().equals(left));
    assertTrue(comp.queryRight().equals(right));
    assertTrue(comp.toString().equals("(>= (+ 3 i7) i4)"));
    assertTrue(SmtProblem.createLeq(left, right).toString().equals("(>= i4 (+ 3 i7))"));
  }

  @Test
  public void testEquality() {
    Constraint comp = SmtProblem.createSmaller(new IVar(2), new IValue(2));
    assertTrue(comp.equals(SmtProblem.createGreater(new IValue(2), new IVar(2))));
    assertFalse(comp.equals(SmtProblem.createGreater(new IVar(2), new IValue(2))));
    Constraint comp2 = SmtProblem.createGeq(new IValue(2), new IVar(2));
    assertFalse(comp.equals(comp2));
    assertFalse(comp2.equals(comp));
  }

  @Test
  public void testLegalEvaluate() {
    IntegerExpression plus = new Addition(new IValue(3), new Addition(new IValue(12), new IValue(-2)));
    Constraint comp = SmtProblem.createGreater(plus, new IValue(12));
    comp = SmtProblem.createGreater(plus, new IValue(13));
    assertFalse(comp.evaluate());
    comp = SmtProblem.createGeq(plus, new IValue(13));
    assertTrue(comp.evaluate());
    comp = SmtProblem.createGeq(new IValue(12), plus);
    assertFalse(comp.evaluate());
  }
}