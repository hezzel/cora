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

  @Test
  public void testCovers() {
    RuleRestrictions nothing = new RuleRestrictions(RuleRestrictions.LVL_FIRSTORDER, false, false,
                                                    false, RuleRestrictions.ROOT_FUNCTION);
    RuleRestrictions anything = new RuleRestrictions(RuleRestrictions.LVL_META, true, true,
                                                    true, RuleRestrictions.ROOT_ANY);
    assertTrue(nothing.checkCoverage(nothing) == null);
    assertTrue(nothing.checkCoverage(anything).equals(
      "rule level is limited to first-order terms, not meta-terms"));
    RuleRestrictions a = new RuleRestrictions(RuleRestrictions.LVL_APPLICATIVE, true, true,
                                              false, RuleRestrictions.ROOT_THEORY);
    RuleRestrictions b = new RuleRestrictions(RuleRestrictions.LVL_LAMBDA, false, false,
                                              true, RuleRestrictions.ROOT_THEORY);
    RuleRestrictions c = new RuleRestrictions(RuleRestrictions.LVL_APPLICATIVE, true, false,
                                              true, RuleRestrictions.ROOT_ANY);
    RuleRestrictions d = new RuleRestrictions(RuleRestrictions.LVL_META, true, true, false,
                                              RuleRestrictions.ROOT_ANY);
    assertTrue(a.checkCoverage(b).equals(
      "rule level is limited to applicative terms, not true terms"));
    assertTrue(a.checkCoverage(c).equals(
      "left-hand side should have a function symbol as root, not anything else"));
    assertTrue(b.checkCoverage(a).equals(
      "use of theory symbols / constraints is not supported"));
    assertTrue(c.checkCoverage(a).equals(
      "use of tuples (or any occurrence of product types) is not supported"));
    assertTrue(d.checkCoverage(b).equals(
      "left-hand side should be a pattern"));
  }
}

