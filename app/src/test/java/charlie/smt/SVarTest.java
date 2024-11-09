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

public class SVarTest {
  @Test
  public void testBasicsNoName() {
    SVar x = new SVar(12);
    assertTrue(x.queryName().equals("s12"));
    assertTrue(x.toString().equals("s12"));
    assertTrue(x.toSmtString().equals("s12"));
  }

  @Test
  public void testBasicsWithName() {
    SVar x = new SVar(12, "xx");
    assertTrue(x.queryName().equals("[xx]"));
    assertTrue(x.toString().equals("[xx]"));
    assertTrue(x.toSmtString().equals("s12"));
  }

  @Test
  public void testComparison() {
    SVar x = new SVar(12);
    assertTrue(x.compareTo(new SVar(12)) == 0);
    assertTrue(x.equals(new SVar(12)));
    assertTrue(x.compareTo(new SVar(13)) < 0);
    assertTrue(x.compareTo(new SVar(3)) > 0);
    assertTrue(x.compareTo(new SValue("12")) > 0);

    assertTrue(x.hashCode() == (new SVar(12)).hashCode());
    assertTrue(x.hashCode() != (new SVar(13)).hashCode());
    assertTrue(x.hashCode() %2 != (new SValue("test")).hashCode() % 2);
  }
}

