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

public class NotTest {
  @Test
  public void testToString() {
    IntegerExpression left = new Addition(new IValue(3), new IVar(7));
    IntegerExpression right = new IVar(4);
    Constraint comp = SmtProblem.createGreater(left, right);
    Constraint neg = SmtProblem.createNegation(comp);
    assertTrue(neg.toString().equals("(not (> (+ 3 i7) i4))"));
  }

  @Test
  public void testEquality() {
    Constraint comp = SmtProblem.createSmaller(new IVar(2), new IValue(2));
    Constraint neg = SmtProblem.createNegation(comp);
    assertTrue(neg.equals(SmtProblem.createNegation(comp)));
    assertFalse(neg.equals(SmtProblem.createGeq(new IValue(2), new IVar(2))));
    assertFalse(neg.equals(SmtProblem.createNegation(new BVar(3))));
  }

  @Test
  public void testLegalEvaluate() {
    Constraint c = SmtProblem.createNegation(new Truth());
    assertFalse(c.evaluate());
    c = new Not(SmtProblem.createGreater(new IValue(3), new IValue(3)));
    assertTrue(c.evaluate());
  }

  @Test
  public void testQueryChild() {
    Not n = new Not(SmtProblem.createGeq(new IVar(1), new IValue(3)));
    assertTrue(n.queryChild().toString().equals("(>= i1 3)"));
  }
}
