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
    assertTrue(y.hashCode() == (new NBVar(new BVar(12))).hashCode());
    assertTrue(y.hashCode() != (new NBVar(new BVar(13))).hashCode());
  }


  @Test
  public void testComparison() {
    NBVar x = new NBVar(new BVar(12));
    BVar a = new BVar(11);
    BVar b = new BVar(12);
    BVar c = new BVar(13);
    assertTrue(x.compareTo(a) > 0);
    assertTrue(x.compareTo(b) > 0);
    assertTrue(x.compareTo(c) < 0);
    assertTrue(x.compareTo(new NBVar(a)) > 0);
    assertTrue(x.compareTo(new NBVar(b)) == 0);
    assertTrue(x.compareTo(new NBVar(c)) < 0);
  }

  @Test
  public void testEvaluate() {
    BVar x = new BVar(3);
    NBVar nx = new NBVar(x);
    assertThrows(charlie.exceptions.SmtEvaluationException.class, () -> nx.evaluate());
  }
}
