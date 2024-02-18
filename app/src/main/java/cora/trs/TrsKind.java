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

import static cora.trs.TrsProperties.*;

/**
 * The TrsKind class tracks properties of a TRS.
 *
 * There are two kinds of properties.  The first kind, consisting of three properties, consider
 * the kind of terms this TrsKind is expected to admit:
 *
 * - level: one of the TermLevel constants: whether terms are first-order, higher-order applicative,
 *   or higher-order with lambda allowance
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
  private String _name;
  private TermLevel _level;
  private boolean _theories;
  private boolean _tuples;
  private RuleRestrictions _rules;

  /**
   * Sets up the TRS kind with the given properties, by deriving the restrictions on terms from the
   * restrictions on rules.
   * (If the rule level is Level.META, then the term level is TermLevel.LAMBDA; everything else is
   * directly taken along.)
   */
  TrsKind(String name, Level level, Constrained theories, Products tuples, Lhs pattern, Root root) {
    _name = name;
    _level = switch(level) {
      case Level.FIRSTORDER -> TermLevel.FIRSTORDER;
      case Level.APPLICATIVE -> TermLevel.APPLICATIVE;
      case Level.LAMBDA -> TermLevel.LAMBDA;
      case Level.META ->TermLevel.LAMBDA;
    };
    _theories = (theories == Constrained.YES);
    _tuples = (tuples == Products.ALLOWED);
    _rules = new RuleRestrictions(level, theories, tuples, pattern, root);
  }

  /** Private helper constructor for updateRestrictions. */
  private TrsKind(String name, TermLevel lvl, boolean theories, boolean tuples,
                  RuleRestrictions restr) {
    _name = name;
    _level = lvl;
    _theories = theories;
    _tuples = tuples;
    _rules = restr;
  }

  /**
   * This returns a copy of the current TrsKind, but with _rules replaced by the given restrictions
   * object.  Note that the object is not copied; it becomes the property of the current TrsKind.
   */
  TrsKind updateRestrictions(RuleRestrictions restrictions) {
    return new TrsKind(_name, _level, _theories, _tuples, restrictions);
  }

  String queryName() {
    return _name;
  }

  RuleRestrictions queryRestrictions() {
    return _rules;
  }

  boolean includeTheories() {
    return _theories;
  }

  boolean includeTuples() {
    return _tuples;
  }

  boolean termsFirstOrder() {
    return _level == TermLevel.FIRSTORDER;
  }

  boolean termsApplicative() {
    return _level.compareTo(TermLevel.APPLICATIVE) <= 0;
  }

  boolean termsIncludeLambda() {
    return _level.compareTo(TermLevel.LAMBDA) >= 0;
  }

  /** For debugging purposes */
  public String toString() {
    return _name + " (term level = " + _level + "; theories = " + _theories + "; tuples = " +
      _tuples + ") with rule restrictions " + _rules.toString();
  }
}

