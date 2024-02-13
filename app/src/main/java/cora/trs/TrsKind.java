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

/**
 * The TrsKind class tracks properties of a TRS.
 *
 * There are three kinds of properties.  The first kind, consisting of three properties, consider
 * the kind of terms this TrsKind is expected to admit:
 *
 * - level: one of LVL_FIRSTORDER, LVL_APPLICATIVE, or LVL_LAMBDA: whether terms are first-order,
 *   higher-order applicative, or higher-order with lambda allowance
 * - theories: true if values and calculation symbols are allowed to occur in terms, false if not
 *   (this currently includes any theory supported by Cora, and no custom ones)
 * - tuples: true if tuples and product types are allowed to occur in terms, false if all types in
 *   the TRS must be constructed without using tuples
 * Note: the highest value of each of these properties corresponds to a rule scheme, which is
 * included in a TRS if and only if that option is supported:
 * - level = LVL_LAMBDA causes Beta to be included
 * - theories = true causes Calc to be included
 * - tuples = true causes Projection to be included
 *
 * The second kind considers restrictions on the rules.
 * @see RuleRestrictions
 *
 * Every TrsKind is immutable.
 */
public class TrsKind {
  public static final int LVL_FIRSTORDER            = RuleRestrictions.LVL_FIRSTORDER;
  public static final int LVL_APPLICATIVE           = RuleRestrictions.LVL_APPLICATIVE;
  public static final int LVL_LAMBDA                = RuleRestrictions.LVL_LAMBDA;
  public static final int LVL_META                  = RuleRestrictions.LVL_META;
  public static final int THEORIES_NONE             = 21;
  public static final int THEORIES_YES              = 22;
  public static final int PRODUCTS_DISALLOWED       = 31;
  public static final int PRODUCTS_ALLOWED          = 32;
  public static final int ROOT_FUNCTION             = RuleRestrictions.ROOT_FUNCTION;
  public static final int ROOT_THEORY               = RuleRestrictions.ROOT_THEORY;
  public static final int ROOT_ANY                  = RuleRestrictions.ROOT_ANY;
  public static final int LHS_PATTERNS              = 41;
  public static final int LHS_NONPATTERNS           = 42;

  private String _name;
  private int _level;  // one of LVL_FIRSTORDER, LVL_APPLICATIVE or LVL_LAMBDA
  private boolean _theories;
  private boolean _tuples;
  private RuleRestrictions _rules;

  /**
   * Sets up the TRS kind with the given properties, as follows:
   * - for each of LVL_, THEORIES_, PRODUCTS_, ROOT_ or LHS_ one constant should be given (if more
   *   then one is given, all but the last is ignored; if one is not given, the minimal possible
   *   value is assumed)
   * - the LVL constant *both* indicates the level allowed for terms (with LVL_META implying that
   *   terms are allowed to have lambda), *and* the maximum level for rule construction
   * - the THEORIES and PRODUCTS constants also indicate both whether these structures are allowd
   *   in term formation in general, and in the rules
   * - the ROOT_ and LHS constants are directly stored as rule restrictions
   */
  TrsKind(String name, int ...properties) {
    int ruleLevel = LVL_FIRSTORDER;
    int rootStatus = ROOT_FUNCTION;
    boolean patternfree = false;
    _level = LVL_FIRSTORDER;
    _theories = false;
    _tuples = false;
    _name = name;
    for (int prop : properties) {
      if (prop >= LVL_FIRSTORDER && prop <= LVL_LAMBDA) { _level = ruleLevel = prop; }
      else if (prop == LVL_META) { _level = LVL_LAMBDA; ruleLevel = prop; }
      else if (prop == THEORIES_NONE) { _theories = false; }
      else if (prop == THEORIES_YES) { _theories = true; }
      else if (prop == PRODUCTS_DISALLOWED) { _tuples = false; }
      else if (prop == PRODUCTS_ALLOWED) { _tuples = true; }
      else if (prop >= ROOT_FUNCTION && prop <= ROOT_ANY) { rootStatus = prop; }
      else if (prop == LHS_PATTERNS) { patternfree = false; }
      else if (prop == LHS_NONPATTERNS) { patternfree = true; }
      else throw new Error("Illegal property: " + prop);
    }
    _rules = new RuleRestrictions(ruleLevel, _theories, _tuples, patternfree, rootStatus);
  }

  String queryName() {
    return _name;
  }

  RuleRestrictions queryRestrictions() {
    return _rules;
  }
}

