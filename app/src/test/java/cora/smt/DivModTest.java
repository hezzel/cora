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
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class DivModTest {
  @Test
  public void testDivisionBasics() {
    Division division = new Division(new Addition(new IValue(-4), new IVar(1)), new IValue(5));
    assertTrue(division.queryNumerator().equals(new Addition(new IValue(-4), new IVar(1))));
    assertTrue(division.queryDenominator().equals(new IValue(5)));
    assertTrue(division.toString().equals("(div (+ (- 4) i1) 5)"));
  }

  @Test
  public void testModuloBasics() {
    Modulo modulo = new Modulo(new Minus(new IVar(2)), new Multiplication(new IValue(2), new IVar(3)));
    assertTrue(modulo.queryNumerator().equals(new Minus(new IVar(2))));
    assertTrue(modulo.queryDenominator().equals(new Multiplication(new IValue(2), new IVar(3))));
    assertTrue(modulo.toString().equals("(mod (- i2) (* 2 i3))"));
  }
  
  @Test
  public void testBouteEvaluate() {
    // tests whether divide and modulo follow the definitions by Boute
    for (int num = -5; num <= 5; num++) {
      for (int denom = -3; denom <= 3; denom++) {
        int d = (new Division(new IValue(num), new IValue(denom))).evaluate();
        int m = (new Modulo(new IValue(num), new IValue(denom))).evaluate();
        String situation = "" + num + " / " + denom + " = " + d + " and " +
                                num + " % " + denom + " = " + m;
        if (denom == 0) {
          assertTrue(d == 0, situation + " (div not 0)");
          assertTrue(m == 0, situation + " (mod not 0)");
        }
        else {
          assertTrue(0 <= m, situation + " (mod too small)");
          assertTrue(m < (denom < 0 ? -denom : denom), situation + " (mod too large)");
          assertTrue(d * denom + m == num, situation + " (rule violated)");
        }
      }
    }
  }

  @Test
  public void testEquality() {
    IntegerExpression d1 = new Division(new IValue(3), new IVar(2));
    IntegerExpression d2 = new Division(new IValue(3), new IVar(2));
    IntegerExpression d3 = new Division(new IValue(3), new IVar(3));
    IntegerExpression m1 = new Modulo(new IValue(3), new IVar(2));
    IntegerExpression m2 = new Modulo(new IValue(3), new IVar(2));
    IntegerExpression m3 = new Modulo(new IValue(3), new IVar(3));
    assertTrue(d1.equals(d2));
    assertTrue(m1.equals(m2));
    assertFalse(d1.equals(d3));
    assertFalse(m1.equals(m3));
    assertFalse(d1.equals(m1));
    assertFalse(m1.equals(d1));
  }
}
