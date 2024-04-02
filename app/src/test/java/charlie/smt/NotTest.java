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

public class NotTest {
  @Test
  public void testToString() {
    IntegerExpression left = new Addition(new IValue(3), new IVar(7));
    IntegerExpression right = new IVar(4);
    Constraint comp = SmtFactory.createGreater(left, right);
    Constraint neg = SmtFactory.createNegation(comp);
    assertTrue(neg.toSmtString().equals("(not (>= (+ 3 i7 (- 1) (- i4)) 0))"));
    assertTrue(neg.toString().equals("not (2 + i7 >= i4)"));
  }

  @Test
  public void testEquality() {
    Constraint comp = SmtFactory.createSmaller(new IVar(2), new IValue(2));
    Constraint neg = SmtFactory.createNegation(comp);
    assertTrue(neg.equals(SmtFactory.createNegation(comp)));
    assertFalse(neg.equals(SmtFactory.createGeq(new IValue(2), new IVar(2))));
    assertFalse(neg.equals(SmtFactory.createNegation(new BVar(3))));
  }

  @Test
  public void testLegalEvaluate() {
    Constraint c = SmtFactory.createNegation(new Truth());
    assertFalse(c.evaluate());
    c = new Not(SmtFactory.createGreater(new IValue(3), new IValue(3)));
    assertTrue(c.evaluate());
  }

  @Test
  public void testQueryChild() {
    Not n = new Not(SmtFactory.createGeq(new IVar(1), new IValue(3)));
    assertTrue(n.queryChild().toString().equals("i1 >= 3"));
  }
}
