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

public class BValueTest {
  @Test
  public void testBasics() {
    Constraint x = new Truth();
    Constraint y = new Falsehood();
    assertTrue(x.evaluate());
    assertFalse(y.evaluate());
    assertTrue(x.toString().equals("true"));
    assertTrue(y.toString().equals("false"));
  }

  @Test
  public void testEquality() {
    Constraint x = new Truth();
    Constraint y = new Falsehood();
    assertTrue(x.equals(new Truth()));
    assertTrue(x.equals(x));
    assertFalse(x.equals(y));
    assertTrue(y.equals(new Falsehood()));
    assertTrue(y.equals(y));
    assertFalse(y.equals(x));
    assertFalse(y.equals(new Geq0(new IValue(1), new IValue(2))));

    assertTrue(x.hashCode() != y.hashCode());
    assertTrue(x.hashCode() == 1);
    assertTrue(y.hashCode() == 2);
  }
}
