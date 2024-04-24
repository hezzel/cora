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

public class IValueTest {
  @Test
  public void testBasics() {
    IValue x = new IValue(-3);
    assertTrue(x.evaluate() == -3);
    assertTrue(x.toString().equals("-3"));
    assertTrue(x.toSmtString().equals("(- 3)"));
    assertTrue(x.multiply(5).equals(new IValue(-15)));
    assertTrue(x.add(5).equals(new IValue(2)));
    assertTrue(x.negate().equals(new IValue(3)));
    assertTrue(x.isSimplified());
  }

  @Test
  public void testComparison() {
    IValue x = new IValue(3);
    assertTrue(x.compareTo(new IValue(3)) == 0);
    assertTrue(x.equals(new IValue(3)));
    assertTrue(x.compareTo(new IValue(-3)) > 0);
    assertFalse(x.equals(new IValue(-3)));
    assertTrue(x.compareTo(new IValue(4)) < 0);
    assertFalse(x.equals(new IValue(4)));
    assertTrue(x.compareTo(new CMult(1, new IValue(1))) < 0);
  }
}
