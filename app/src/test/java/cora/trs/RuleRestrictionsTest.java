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

import cora.trs.TrsProperties.*;

public class RuleRestrictionsTest {
  @Test
  public void testBasicCreate() {
    RuleRestrictions rest = new RuleRestrictions(Level.APPLICATIVE, Constrained.YES,
                                                 Products.DISALLOWED, Lhs.NONPATTERN, Root.ANY);
    assertTrue(rest.queryLevel() == Level.APPLICATIVE);
    assertTrue(rest.theoriesUsed());
    assertFalse(rest.productsUsed());
    assertTrue(rest.patternStatus() == Lhs.NONPATTERN);
    assertTrue(rest.rootStatus() == Root.ANY);
  }

  @Test
  public void testCovers() {
    RuleRestrictions nothing = new RuleRestrictions(Level.FIRSTORDER, Constrained.YES,
                                                    Products.DISALLOWED, Lhs.PATTERN,
                                                    Root.FUNCTION);
    RuleRestrictions anything = new RuleRestrictions(Level.META, Constrained.YES, Products.ALLOWED,
                                                     Lhs.NONPATTERN, Root.ANY);
    assertTrue(nothing.checkCoverage(nothing) == null);
    assertTrue(nothing.checkCoverage(anything).equals(
      "rule level is limited to first-order terms, not meta-terms"));
    RuleRestrictions a = new RuleRestrictions(Level.APPLICATIVE, Constrained.YES, Products.ALLOWED,
                                              Lhs.PATTERN, Root.THEORY);
    RuleRestrictions b = new RuleRestrictions(Level.LAMBDA, Constrained.NO, Products.DISALLOWED,
                                              Lhs.SEMIPATTERN, Root.THEORY);
    RuleRestrictions c = new RuleRestrictions(Level.APPLICATIVE, Constrained.YES,
                                              Products.DISALLOWED, Lhs.SEMIPATTERN, Root.ANY);
    RuleRestrictions d = new RuleRestrictions(Level.META, Constrained.YES, Products.ALLOWED,
                                              Lhs.PATTERN, Root.ANY);
    assertTrue(a.checkCoverage(b).equals(
      "rule level is limited to applicative terms, not true terms"));
    assertTrue(a.checkCoverage(c).equals(
      "left-hand side should have a function symbol as root, not anything else"));
    assertTrue(b.checkCoverage(a).equals(
      "use of theory symbols / constraints is not supported"));
    assertTrue(c.checkCoverage(a).equals(
      "use of tuples (or any occurrence of product types) is not supported"));
    assertTrue(d.checkCoverage(b).equals(
      "left-hand side should be a pattern, not a semi-pattern"));
  }

  @Test
  public void testSupremum() {
    RuleRestrictions a = new RuleRestrictions(Level.APPLICATIVE, Constrained.NO,
                                              Products.ALLOWED, Lhs.SEMIPATTERN, Root.ANY);
    RuleRestrictions b = new RuleRestrictions(Level.META, Constrained.YES, Products.DISALLOWED,
                                              Lhs.PATTERN, Root.THEORY);
    // doing it from either side should result in the same
    RuleRestrictions c = a.supremum(b);
    RuleRestrictions d = b.supremum(a);
    assertTrue(c.queryLevel() == Level.META);
    assertTrue(d.queryLevel() == Level.META);
    assertTrue(c.theoriesUsed());
    assertTrue(d.theoriesUsed());
    assertTrue(c.productsUsed());
    assertTrue(d.productsUsed());
    assertTrue(c.patternStatus() == Lhs.SEMIPATTERN);
    assertTrue(d.patternStatus() == Lhs.SEMIPATTERN);
    assertTrue(c.rootStatus() == Root.ANY);
    assertTrue(d.rootStatus() == Root.ANY);
  }
}

