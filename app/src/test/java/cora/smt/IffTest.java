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

import java.util.ArrayList;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class IffTest {
  @Test
  public void testToString() {
    IntegerExpression left = new IVar(7);
    IntegerExpression right = new Addition(new IValue(3), new IVar(1));
    Constraint comp = SmtFactory.createGreater(left, right);
    Constraint bvar = new BVar(9);
    Constraint iff = SmtFactory.createIff(comp, bvar);
    assertTrue(iff.toString().equals("(= (> i7 (+ 3 i1)) b9)"));
  }

  @Test
  public void testEquality() {
    Constraint comp = SmtFactory.createSmaller(new IVar(2), new IValue(2));
    Constraint neg = SmtFactory.createNegation(comp);
    Constraint other = SmtFactory.createGeq(new IValue(3), new IVar(3));
    Constraint iff = SmtFactory.createIff(neg, other);
    assertTrue(iff.equals(iff));
    assertTrue(iff.equals(SmtFactory.createIff(neg, other)));
    assertFalse(iff.equals(SmtFactory.createIff(other, neg)));
    assertFalse(iff.equals(SmtFactory.createIff(neg, neg)));
    assertFalse(iff.equals(SmtFactory.createIff(other, other)));
  }

  @Test
  public void testLegalEvaluate() {
    Constraint a = SmtFactory.createNegation(new Truth());
    Constraint b = new Falsehood();
    Constraint iff1 = new Iff(a, b);
    Constraint iff2 = new Iff(SmtFactory.createNegation(b), a);
    assertTrue(iff1.evaluate());
    assertFalse(iff2.evaluate());
  }

  @Test
  public void testQueryParts() {
    Not n = new Not(SmtFactory.createGeq(new IVar(1), new IValue(3)));
    BVar a = new BVar(7);
    Iff i = new Iff(a, n);
    assertTrue(i.queryLeft().equals(a));
    assertTrue(i.queryRight().equals(n));
  }
}
