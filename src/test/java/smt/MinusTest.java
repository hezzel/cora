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

public class MinusTest {
  @Test
  public void testBasics() {
    Minus minus = new Minus(new Addition(new IValue(-4), new IVar(1)));
    assertTrue(minus.queryChild().equals(new Addition(new IValue(-4), new IVar(1))));
    assertTrue(minus.toString().equals("(- (+ (- 4) i1))"));
  }

  @Test
  public void testLegalEvaluate() {
    IntegerExpression minus = new Minus(new Minus(new Minus(new Multiplication(
      new IValue(3), new IValue(-5)))));
    assertTrue(minus.evaluate() == 15);
  }

  @Test
  public void testEquality() {
    IntegerExpression m1 = new Minus(new Addition(new IValue(-4), new IVar(1)));
    IntegerExpression m2 = new Minus(new Addition(new IValue(-4), new IVar(1)));
    IntegerExpression m3 = new Minus(new Addition(new IValue(-3), new IVar(1)));
    IntegerExpression p = new Addition(new Addition(new IValue(-3), new IVar(1)), new IVar(3));
    assertTrue(m1.equals(m2));
    assertFalse(m1.equals(m3));
    assertFalse(m1.equals(p));
  }
}
