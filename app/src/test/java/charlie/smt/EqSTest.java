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

public class EqSTest {
  @Test
  public void testBasics() {
    SVar x = new SVar(3, "x");
    SValue v = new SValue("test");
    EqS eqs = new EqS(x, v);
    assertTrue(eqs.toString().equals("[x] = \"test\""));
    assertTrue(eqs.queryLeft() == x);
    assertTrue(eqs.queryRight() == v);
    assertTrue(eqs.negate().toString().equals("[x] # \"test\""));
    EqS eqs2 = new EqS(v, x);
    assertTrue(eqs2.toString().equals("[x] = \"test\""));
    assertTrue(eqs.equals(eqs2));
  }

  @Test
  public void testSimplify() {
    SVar x1 = new SVar(3, "x");
    SVar x2 = new SVar(3, "x");
    SVar y = new SVar(4, "y");
    SValue a = new SValue("test");
    SValue b = new SValue("testing");
    SValue c = new SValue("test");
    
    EqS eqs1 = new EqS(x1, x2);       // x == x
    EqS eqs2 = new EqS(x1, y);        // x == y
    EqS eqs3 = new EqS(x1, a);        // x == "test"
    EqS eqs4 = new EqS(a, b);         // "test" == "testing"
    EqS eqs5 = new EqS(a, c);         // "test" == "test"
    assertFalse(eqs1.isSimplified());
    assertTrue(eqs2.isSimplified());
    assertTrue(eqs3.isSimplified());
    assertFalse(eqs4.isSimplified());
    assertFalse(eqs5.isSimplified());
    assertTrue(eqs1.simplify().equals(new Truth()));
    assertTrue(eqs2.simplify().equals(eqs2));
    assertTrue(eqs3.simplify().equals(eqs3));
    assertTrue(eqs4.simplify().equals(new Falsehood()));
    assertTrue(eqs5.simplify().equals(new Truth()));
  }

  @Test
  public void testEvaluate() {
    SValue a = new SValue("a");
    SValue b = new SValue("b");
    SValue c = new SValue("a");
    Constraint eq1 = new EqS(a, b);
    Constraint eq2 = new EqS(a, c);
    assertFalse(eq1.evaluate());
    assertTrue(eq2.evaluate());
  }

  @Test
  public void testComparison() {
    SVar x = new SVar(12);
    SVar y = new SVar(13);
    SValue v = new SValue("bca");

    Constraint eq1 = new EqS(x, v);
    Constraint eq2 = new EqS(y, v);
    assertTrue(eq1.compareTo(eq2) <= -2);
    assertTrue(eq2.compareTo(eq1) >= 2);
    Constraint un1 = new UneqS(x, v);
    Constraint un2 = new UneqS(y, v);
    Constraint un3 = new UneqS(y, new SValue("cba"));
    assertTrue(eq1.compareTo(un1) == -1);
    assertTrue(eq1.compareTo(un2) <= -2);
    assertTrue(eq1.compareTo(un3) <= -2);
    assertTrue(eq2.compareTo(un1) >= 2);
  }
}
