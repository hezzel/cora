/**************************************************************************************************
 Copyright 2024 Cynthia Kop

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

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;

public class ConstantMultiplicationTest {
  @Test
  public void testBasics() {
    ConstantMultiplication cm =
      new ConstantMultiplication(-1, new Addition(new IValue(-4), new IVar(1)));
    assertTrue(cm.queryChild().equals(new Addition(new IValue(-4), new IVar(1))));
    assertTrue(cm.toString().equals("(- (+ (- 4) i1))"));
  }

  @Test
  public void testLegalEvaluate() {
    IntegerExpression minus =
      new ConstantMultiplication(-2,
      new ConstantMultiplication(1,
      new ConstantMultiplication(3,
      new Multiplication(new IValue(3), new IValue(-5)))));
    assertTrue(minus.evaluate() == 90);
  }

  @Test
  public void testMultiply() {
    IVar x = new IVar(2);
    IntegerExpression cm = new ConstantMultiplication(-1, x);
    assertTrue(cm.multiply(0).equals(new IValue(0)));
    assertTrue(cm.multiply(1).equals(cm));
    assertTrue(cm.multiply(-1).equals(x));
    assertTrue(cm.multiply(2).equals(new ConstantMultiplication(-2, x)));
    assertTrue(cm.multiply(-2).equals(new ConstantMultiplication(2, x)));
    assertTrue(cm.negate().equals(x));
  }

  @Test
  public void testToString() {
    IntegerExpression xy = new Multiplication(new IVar(1), new IVar(2));
    ConstantMultiplication a = new ConstantMultiplication(-2, xy);
    ConstantMultiplication b = new ConstantMultiplication(-1, xy);
    ConstantMultiplication c = new ConstantMultiplication(0, xy);
    ConstantMultiplication d = new ConstantMultiplication(1, xy);
    ConstantMultiplication e = new ConstantMultiplication(2, xy);
    assertTrue(a.toString().equals("(* (- 2) (* i1 i2))"));
    assertTrue(b.toString().equals("(- (* i1 i2))"));
    assertTrue(c.toString().equals("(* 0 (* i1 i2))"));
    assertTrue(d.toString().equals("(* 1 (* i1 i2))"));
    assertTrue(e.toString().equals("(* 2 (* i1 i2))"));
  }

  @Test
  public void testComparison() {
    IntegerExpression mf = new IValue(-4);
    IntegerExpression mt = new IValue(-3);
    IntegerExpression x = new IVar(1);
    IntegerExpression m1 = new ConstantMultiplication(-2, new Addition(mf, x));
    IntegerExpression m2 = new ConstantMultiplication(-2, new Addition(mf, x));
    IntegerExpression m3 = new ConstantMultiplication(-2, new Addition(mt, x));
    IntegerExpression m4 = new Multiplication(new IValue(-2), new Addition(mf, x));
    IntegerExpression p = new Addition(new IValue(8), new ConstantMultiplication(-2, x));
    assertTrue(m1.compareTo(m2) == 0);
    assertTrue(m1.compareTo(m3) < 0);
    assertTrue(m1.compareTo(m4) != 0);
    assertTrue(m1.compareTo(m4) == -m4.compareTo(m1));
    assertTrue(m1.compareTo(p) != 0);
    assertTrue(m1.compareTo(p) == -p.compareTo(m1));
  }
}
