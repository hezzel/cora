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

import cora.exceptions.IllegalArgumentError;
import cora.exceptions.IllegalRuleError;
import cora.terms.Term;

/**
 * The TrsFactory is used to create rules and different kinds of TRSs.
 */
public class TrsFactory {
  public static final TrsKind MSTRS =
    new TrsKind("MSTRS", TrsKind.LVL_FIRSTORDER, TrsKind.THEORIES_NONE,
                TrsKind.PRODUCTS_DISALLOWED, TrsKind.ROOT_FUNCTION);
  public static final TrsKind STRS =
    new TrsKind("STRS", TrsKind.LVL_APPLICATIVE, TrsKind.THEORIES_NONE,
                TrsKind.PRODUCTS_DISALLOWED, TrsKind.ROOT_ANY, TrsKind.LHS_NONPATTERNS);
  public static final TrsKind CFS =
    new TrsKind("CFS", TrsKind.LVL_LAMBDA, TrsKind.THEORIES_NONE,
                TrsKind.PRODUCTS_DISALLOWED, TrsKind.ROOT_FUNCTION, TrsKind.LHS_PATTERNS);
  public static final TrsKind AMS =
    new TrsKind("AMS", TrsKind.LVL_META, TrsKind.THEORIES_NONE,
                TrsKind.PRODUCTS_DISALLOWED, TrsKind.ROOT_FUNCTION, TrsKind.LHS_NONPATTERNS);
  public static final TrsKind LCTRS =
    new TrsKind("LCTRS", TrsKind.LVL_META, TrsKind.THEORIES_YES,
                TrsKind.PRODUCTS_DISALLOWED, TrsKind.ROOT_ANY);
  public static final TrsKind LCSTRS =
    new TrsKind("LCSTRS", TrsKind.LVL_META, TrsKind.THEORIES_YES,
                TrsKind.PRODUCTS_DISALLOWED, TrsKind.ROOT_THEORY, TrsKind.LHS_PATTERNS);
  public static final TrsKind CORA =
    new TrsKind("Cora-TRS", TrsKind.LVL_META, TrsKind.THEORIES_YES,
                TrsKind.PRODUCTS_ALLOWED, TrsKind.ROOT_ANY, TrsKind.LHS_NONPATTERNS);

  /**
   * Check if the given rule is allowed in the given kind of TRS.  If not, throws an
   * IllegalRuleError.
   */
  private static void checkRestrictions(Rule rule, TrsKind kind) {
    String problem = kind.queryRestrictions().checkCoverage(rule.queryProperties());
    if (problem == null) return;
    throw new IllegalRuleError("The rule " + rule.toString() + " is not allowed to occur in " +
      kind.queryName() + "s: " + problem + ".");
  }

  /**
   * This function creates an unconstrained rule left → right.
   * The rule is checked against the given TRS kind: if the rule is not allowed in the give nkind
   * of TRS, then an IllegalRuleError is thrown.
   */
  public static Rule createRule(Term left, Term right, TrsKind restrictions) {
    Rule rule = new Rule(left, right);
    checkRestrictions(rule, restrictions);
    return rule;
  }

  /**
   * This function creates a constrained rule left → right | constraint.
   * The rule is checked against the given TRS kind: if the rule is not allowed in the given kind
   * of TRS, then an IllegalRuleError is thrown.
   */
  public static Rule createRule(Term left, Term right, Term constraint, TrsKind restrictions) {
    Rule rule = new Rule(left, right, constraint);
    checkRestrictions(rule, restrictions);
    return rule;
  }
}

