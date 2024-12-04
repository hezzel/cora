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

public class UneqSTest {
  @Test
  public void testBasics() {
    SVar x = new SVar(3, "x");
    SValue v = new SValue("test");
    UneqS uns = new UneqS(x, v);
    assertTrue(uns.toString().equals("[x] # \"test\""));
    assertTrue(uns.queryLeft() == x);
    assertTrue(uns.queryRight() == v);
    assertTrue(uns.negate().toString().equals("[x] = \"test\""));
    UneqS uns2 = new UneqS(v, x);
    assertTrue(uns2.toString().equals("[x] # \"test\""));
    assertTrue(uns.equals(uns2));
  }

  @Test
  public void testSimplify() {
    SVar x1 = new SVar(3, "x");
    SVar x2 = new SVar(3, "x");
    SVar y = new SVar(4, "y");
    SValue a = new SValue("test");
    SValue b = new SValue("testing");
    SValue c = new SValue("test");

    UneqS uns1 = new UneqS(x1, x2);       // x # x
    UneqS uns2 = new UneqS(x1, y);        // x # y
    UneqS uns3 = new UneqS(x1, a);        // x # "test"
    UneqS uns4 = new UneqS(a, b);         // "test" # "testing"
    UneqS uns5 = new UneqS(a, c);         // "test" # "test"
    assertFalse(uns1.isSimplified());
    assertTrue(uns2.isSimplified());
    assertTrue(uns3.isSimplified());
    assertFalse(uns4.isSimplified());
    assertFalse(uns5.isSimplified());
    assertTrue(uns1.simplify().equals(new Falsehood()));
    assertTrue(uns2.simplify().equals(uns2));
    assertTrue(uns3.simplify().equals(uns3));
    assertTrue(uns4.simplify().equals(new Truth()));
    assertTrue(uns5.simplify().equals(new Falsehood()));
  }

  @Test
  public void testEvaluate() {
    SValue a = new SValue("a");
    SValue b = new SValue("b");
    SValue c = new SValue("a");
    Constraint un1 = new UneqS(a, b);
    Constraint un2 = new UneqS(a, c);
    assertTrue(un1.evaluate());
    assertFalse(un2.evaluate());
  }

  @Test
  public void testComparison() {
    SVar x = new SVar(12);
    SVar y = new SVar(13);
    SValue v = new SValue("bca");
    SValue w = new SValue("cba");

    Constraint un1 = new UneqS(x, v);
    Constraint un2 = new UneqS(y, v);
    Constraint un3 = new UneqS(x, w);
    assertTrue(un1.compareTo(un2) <= -2);
    assertTrue(un2.compareTo(un1) >= 2);
    assertTrue(un1.compareTo(un3) <= -2);
    assertTrue(un2.compareTo(un3) >= 2);
    assertTrue(un3.compareTo(un2) <= -2);

    Constraint eq1 = new EqS(x, v);
    Constraint eq2 = new EqS(y, v);
    Constraint eq3 = new EqS(x, w);
    assertTrue(un1.compareTo(eq1) == 1);
    assertTrue(un1.compareTo(eq2) <= -2);
    assertTrue(un2.compareTo(eq1) >= 2);
    assertTrue(un1.compareTo(eq3) <= -2);
    assertTrue(un2.compareTo(eq3) >= 2);
  }
}
