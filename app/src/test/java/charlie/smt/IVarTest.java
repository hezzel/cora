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

public class IVarTest {
  @Test
  public void testBasicsNoName() {
    IVar x = new IVar(12);
    assertTrue(x.queryName().equals("i12"));
    assertTrue(x.toString().equals("i12"));
    assertTrue(x.toSmtString().equals("i12"));
    assertTrue(x.isSimplified());
  }

  @Test
  public void testBasicsWithName() {
    IVar x = new IVar(12, "xx");
    assertTrue(x.queryName().equals("[xx]"));
    assertTrue(x.toString().equals("[xx]"));
    assertTrue(x.toSmtString().equals("i12"));
    assertTrue(x.isSimplified());
  }

  @Test
  public void testMultiplication() {
    IVar x = new IVar(7);
    assertTrue(x.negate().equals(new CMult(-1, x)));
    assertTrue(x.multiply(0).equals(new IValue(0)));
    assertTrue(x.multiply(1).equals(x));
    assertTrue(x.multiply(12).equals(new CMult(12, x)));
  }

  @Test
  public void testComparison() {
    IVar x = new IVar(12);
    assertTrue(x.compareTo(new IVar(12)) == 0);
    assertTrue(x.equals(new IVar(12)));
    assertTrue(x.compareTo(new IVar(13)) < 0);
    assertTrue(x.compareTo(new IVar(3)) > 0);
    // we don't test here against other kinds; this is handled in CMultTest
    assertTrue(x.hashCode() == (new IVar(12)).hashCode());
    assertTrue(x.hashCode() != (new IVar(13)).hashCode());
  }
}

