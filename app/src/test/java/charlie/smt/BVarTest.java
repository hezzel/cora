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
  public void testBasics() {
    BVar x = new BVar(12);
    assertTrue(x.queryIndex() == 12);
    assertTrue(x.toString().equals("b12"));
  }

  @Test
  public void testEquality() {
    BVar x = new BVar(12);
    assertTrue(x.equals(new BVar(12)));
    assertFalse(x.equals(new BVar(13)));
    assertFalse(x.equals(new IVar(12)));
  }

  @Test
  public void testEvaluate() {
    BVar x = new BVar(3);
    assertThrows(charlie.exceptions.SmtEvaluationError.class, () -> x.evaluate());
  }
}
