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

import java.util.List;
import java.util.Collection;
import cora.exceptions.IllegalRuleError;
import cora.utils.Pair;
import cora.terms.Term;
import cora.terms.Variable;
import cora.terms.position.Position;

/**
 * The RuleRestrictions class tracks properties that a rule in a TRS satisfies.  This class is
 * meant for internal use within the trs package, as it is used for error handling and storing
 * properties of TRSs or their rules.
 */
class RuleRestrictions {
  static final int LVL_FIRSTORDER   = 101;
  static final int LVL_APPLICATIVE  = 102;
  static final int LVL_LAMBDA       = 103;
  static final int LVL_META         = 104;

  static final int ROOT_FUNCTION    = 111;
  static final int ROOT_THEORY      = 112;
  static final int ROOT_ANY         = 113;

  static final int LHS_PATTERN      = 121;
  static final int LHS_SEMIPATTERN  = 122;
  static final int LHS_NONPATTERN   = 123;

  private int _level;         // one of the LVL_ constants
  private boolean _theories;  // whether or not this is a "constrained rule"
  private boolean _products;  // whether product types are used in the construction
  private int _pattern;       // whether the lhs is a pattern or semi-pattern
  private int _rootStatus;    // one of the ROOT_ constants

  /**
   * Returns the lowest one of LVL_FIRSTORDER, LVL_APPLICATIVE, LVL_LAMBDA, LVL_META that both left
   * and right hand side of the rule satisfy. (Note: the constraint is NOT considered in this.)
   */
  int queryLevel() { return _level; }

  /**
   * Returns whether theories are used in any way (that is, there is a constraint, a fresh theory
   * variable in the right-hand side, or any use of a value or calculation symbol in the left- or
   * right-hand side).
   */
  boolean theoriesUsed() { return _theories; }

  /**
   * Returns whether product types are used in any way (that is, the left-hand side, right-hand
   * side or the constraint has a subterm whose type contains (or is) a product type.
   */
  boolean productsUsed() { return _products; }

  /** Returns whether the left-hand side is a pattern, semi-pattern or non-pattern. */
  int patternStatus() { return _pattern; }

  /**
   * Returns ROOT_FUNCTION if the root of the left-hand side is a non-theory function symbol,
   * ROOT_CALC if the root of the left-hand side is a theory symbol, and ROOT_ANY if the
   * left-hand side does not have a function symbol as root.
   */
  int rootStatus() { return _rootStatus; }

  /**
   * Constructor that sets up all values in order.  No error checking is done (for instance to see
   * if the given level is indeed one of the permitted constants) because this can only be called
   * from within the trs package.
   */
  RuleRestrictions(int lvl, boolean theories, boolean products, int pattern, int rootstat) {
    _level = lvl;
    _theories = theories;
    _products = products;
    _pattern = pattern;
    _rootStatus = rootstat;
  }

  /** Constructor that sets up the values corresponding to a given rule. */
  RuleRestrictions(Term left, Term right, Term constraint, Collection<Variable> lvars) {
    // level
    if (left.isFirstOrder() && right.isFirstOrder()) _level = LVL_FIRSTORDER;
    else if (left.isApplicative() && right.isApplicative()) _level = LVL_APPLICATIVE;
    else if (left.isTrueTerm() && right.isTrueTerm()) _level = LVL_LAMBDA;
    else _level = LVL_META;
    // pattern restriction
    if (left.isPattern()) _pattern = LHS_PATTERN;
    else if (_level != LVL_META) _pattern = LHS_SEMIPATTERN;
    else if (left.isSemiPattern()) _pattern = LHS_SEMIPATTERN;
    else _pattern = LHS_NONPATTERN;
    // root status
    if (!left.isFunctionalTerm()) _rootStatus = ROOT_ANY;
    else if (left.queryRoot().isTheorySymbol()) _rootStatus = ROOT_THEORY;
    else _rootStatus = ROOT_FUNCTION;
    // theories and products
    _theories = false;
    _products = false;
    if (!lvars.isEmpty()) _theories = true;
    List<Pair<Term,Position>> subterms = left.querySubterms();
    subterms.addAll(right.querySubterms());
    if (!constraint.isValue() || !constraint.toValue().getBool()) {
      _theories = true;
      subterms.addAll(constraint.querySubterms());
    }
    for (int i = 0; i < subterms.size() && !(_theories && _products); i++) {
      Term sub = subterms.get(i).fst();
      if (sub.isFunctionalTerm() && sub.queryRoot().isTheorySymbol()) _theories = true;
      if (sub.queryType().hasProducts()) _products = true;
    }
  }

  /**
   * This checks if all our properties are ≥ than those of other.
   * If so, null is returned.
   * If not, a message is returned explaining the problem.
   */
  String checkCoverage(RuleRestrictions other) {
    if (_level < other._level) {
      String[] kinds = { "first-order ", "applicative ", "true ", "meta-" };
      return "rule level is limited to " + kinds[_level - LVL_FIRSTORDER] + "terms, not " +
        kinds[other._level - LVL_FIRSTORDER] + "terms";
    }
    if (_rootStatus < other._rootStatus) {
      String[] kinds = { "a non-theory symbol", "a function symbol", "anything else" };
      return "left-hand side should have " + kinds[_rootStatus - ROOT_FUNCTION] + " as root, not " +
        kinds[other._rootStatus - ROOT_FUNCTION];
    }
    if (_pattern < other._pattern) {
      String[] kinds = { "pattern", "semi-pattern", "non-pattern" };
      return "left-hand side should be a " + kinds[_pattern - LHS_PATTERN] + ", not a " +
        kinds[other._pattern - LHS_PATTERN];
    }
    if (!_theories && other._theories) {
      return "use of theory symbols / constraints is not supported";
    }
    if (!_products && other._products) {
      return "use of tuples (or any occurrence of product types) is not supported";
    }
    return null;
  }

  /** This returns true iff all our properties are ≥ those of other. */
  boolean covers(RuleRestrictions other) {
    return checkCoverage(other) != null;
  }
}

