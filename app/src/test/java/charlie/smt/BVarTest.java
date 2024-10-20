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

public class BVarTest {
  @Test
  public void testBasicsNoName() {
    BVar x = new BVar(12);
    assertTrue(x.queryIndex() == 12);
    assertTrue(x.queryName().equals("b12"));
    assertTrue(x.toString().equals("b12"));
    assertTrue(x.toSmtString().equals("b12"));
  }

  @Test
  public void testBasicsWithName() {
    BVar x = new BVar(12, "z");
    assertTrue(x.queryIndex() == 12);
    assertTrue(x.queryName().equals("[z]"));
    assertTrue(x.toString().equals("[z]"));
    assertTrue(x.toSmtString().equals("b12"));
  }

  @Test
  public void testNegate() {
    BVar x = new BVar(12);
    assertTrue(x.negate().equals(new NBVar(x)));
    assertTrue(x.negate().toString().equals("!b12"));
    assertTrue(x.negate().toSmtString().equals("(not b12)"));
    BVar y = new BVar(13, "x");
    assertTrue(y.negate().toString().equals("![x]"));
    assertTrue(y.negate().toSmtString().equals("(not b13)"));
  }

  @Test
  public void testEquality() {
    BVar x = new BVar(12);
    assertTrue(x.equals(new BVar(12)));
    assertFalse(x.equals(new BVar(13)));
    assertFalse(x.equals(new IVar(12)));
    assertFalse(x.equals(x.negate()));
    assertTrue(x.hashCode() == (new BVar(12)).hashCode());
    assertTrue(x.hashCode() != (new BVar(13)).hashCode());
    assertTrue(x.hashCode() != (new NBVar(x)).hashCode());
  }

  @Test
  public void testEvaluate() {
    BVar x = new BVar(3);
    assertThrows(charlie.exceptions.SmtEvaluationException.class, () -> x.evaluate());
  }
}
