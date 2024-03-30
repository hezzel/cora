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

package charlie.smt;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;

public class MixedCompareToTest {
  private ArrayList createDifferentIntegerExpressions() {
    IntegerExpression x = new IVar(1);
    IntegerExpression y = new IVar(2);
    IntegerExpression k = new IValue(-3);
    ArrayList<IntegerExpression> arr = new ArrayList<IntegerExpression>();
    arr.add(k);
    arr.add(x);
    arr.add(y);
    arr.add(new Addition(x, y));
    arr.add(new Multiplication(x, y));
    arr.add(new Division(x, y));
    arr.add(new Modulo(x, y));
    return arr;
  }

  @Test
  public void testOrderBetweenIntegerExpressionKindsIsFixed() {
    ArrayList<IntegerExpression> arr = createDifferentIntegerExpressions();
    for (int i = 0; i < arr.size(); i++) {
      IntegerExpression a = arr.get(i);
      assertTrue(a.compareTo(a) == 0);
      for (int j = i+1; j < arr.size(); j++) {
        IntegerExpression b = arr.get(j);
        int comp = a.compareTo(b);
        assertTrue(comp != 0);
        assertTrue(comp == - b.compareTo(a), "comparing " + a + " and " + b);
      }
    }
  }

  int sign(int num) { return num < 0 ? -1 : 1; }

  @Test
  public void testOrderAdaptedForConstantLeft() {
    ArrayList<IntegerExpression> arr = createDifferentIntegerExpressions();
    for (int i = 0; i < arr.size(); i++) {
      IntegerExpression a = arr.get(i);
      IntegerExpression ca = new CMult(2, a);
      assertTrue(a.compareTo(a) == 0);
      for (int j = 0; j < arr.size(); j++) {
        IntegerExpression b = arr.get(j);
        if (i == j) assertTrue(ca.compareTo(b) > 0, "comparing " + ca + " and " + b);
        else assertTrue(sign(a.compareTo(b)) == sign(ca.compareTo(b)),
                        "comparing " + ca + " and " + b);
      }
    }
  }

  @Test
  public void testOrderAdaptedForConstantRight() {
    ArrayList<IntegerExpression> arr = createDifferentIntegerExpressions();
    for (int i = 0; i < arr.size(); i++) {
      IntegerExpression a = arr.get(i);
      IntegerExpression ca = new CMult(2, a);
      assertTrue(a.compareTo(a) == 0);
      for (int j = 0; j < arr.size(); j++) {
        IntegerExpression b = arr.get(j);
        if (i == j) assertTrue(b.compareTo(ca) < 0, "comparing " + b + " and " + ca);
        else assertTrue(sign(b.compareTo(a)) == sign(b.compareTo(ca)),
                        "comparing " + b + " and " + ca);
      }
    }
  }

  @Test
  public void testConstantMinimal() {
    ArrayList<IntegerExpression> arr = createDifferentIntegerExpressions();
    for (int i = 1; i < arr.size(); i++) {
      assertTrue(arr.get(0).compareTo(arr.get(i)) < 0);
      assertTrue(arr.get(i).compareTo(arr.get(0)) > 0);
    }
    IntegerExpression constant = new IValue(5);
    IntegerExpression cmult = new CMult(-1, new IValue(-1));
    assertTrue(constant.compareTo(cmult) < 0);
    assertTrue(cmult.compareTo(constant) > 0);
  }
}

