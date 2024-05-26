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

public class NBVarTest {
  @Test
  public void testBasicsName() {
    BVar x = new BVar(12);
    NBVar nx = new NBVar(x);
    assertTrue(nx.queryIndex() == 12);
    assertTrue(nx.queryName().equals("b12"));
    assertTrue(nx.toString().equals("!b12"));
    assertTrue(nx.toSmtString().equals("(not b12)"));
    assertTrue(nx.negate() == x);
    BVar y = new BVar(12, "xx");
    NBVar ny = new NBVar(y);
    assertTrue(ny.toString().equals("![xx]"));
  }

  @Test
  public void testEquality() {
    BVar x = new BVar(12);
    NBVar y = new NBVar(x);
    assertFalse(x.equals(y));
    assertFalse(y.equals(x));
    assertTrue(y.equals(new NBVar(new BVar(12))));
    assertFalse(y.equals(new NBVar(new BVar(13))));
  }

  @Test
  public void testEvaluate() {
    BVar x = new BVar(3);
    NBVar nx = new NBVar(x);
    assertThrows(charlie.exceptions.SmtEvaluationException.class, () -> nx.evaluate());
  }
}
