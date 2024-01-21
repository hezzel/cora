/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.trs;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class RuleRestrictionsTest {
  @Test
  public void testBasicCreate() {
    RuleRestrictions rest = new RuleRestrictions(RuleRestrictions.LVL_APPLICATIVE, true, false,
                                                 true, RuleRestrictions.ROOT_ANY);
    assertTrue(rest.queryLevel() == RuleRestrictions.LVL_APPLICATIVE);
    assertTrue(rest.theoriesUsed());
    assertFalse(rest.productsUsed());
    assertTrue(rest.leftIsNonPattern());
    assertTrue(rest.rootStatus() == RuleRestrictions.ROOT_ANY);
  }
}

