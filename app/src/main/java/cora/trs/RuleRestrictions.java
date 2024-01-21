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

  private int _level; // one of the LVL_ constants
  private boolean _theories;  // whether or not this is a "constrained rule"
  private boolean _products;  // whether product types are used in the construction
  private boolean _nonPattern; // if the lhs is a pattern or not
  private int _rootStatus; // one of the ROOT_ constants

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

  /** Returns whether or not the left-hand side is a non-pattern. */
  boolean leftIsNonPattern() { return _nonPattern; }

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
  RuleRestrictions(int lvl, boolean theories, boolean products, boolean nonpattern, int rootstat) {
    _level = lvl;
    _theories = theories;
    _products = products;
    _nonPattern = nonpattern;
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
    _nonPattern = !left.isPattern();
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
}

