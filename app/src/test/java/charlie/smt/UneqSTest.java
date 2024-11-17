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

    Constraint un1 = new UneqS(x, v);
    Constraint un2 = new UneqS(y, v);
    assertTrue(un1.compareTo(un2) < 0);
    assertTrue(un2.compareTo(un1) > 0);
  }
}
