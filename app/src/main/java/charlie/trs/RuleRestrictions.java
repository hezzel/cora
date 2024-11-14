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

package charlie.trs;

import java.util.Map;
import java.util.List;
import java.util.Collection;
import charlie.util.Pair;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.Replaceable;
import charlie.terms.ReplaceableList;
import charlie.terms.position.Position;
import charlie.trs.TrsProperties.*;

/**
 * The RuleRestrictions class tracks properties that a rule in a TRS satisfies.  This class is
 * deliberately not public, as it is only meant for internal use within the trs package: it is used
 * for error handling and storing properties of TRSs or their rules.
 */
class RuleRestrictions {
  private Level _level;
  private boolean _theories;
  private boolean _products;
  private Lhs _pattern;
  private Root _rootStatus;
  private FreshRight _fresh;

  /**
   * Returns the lowest level that both left and right hand side of the rule satisfy.
   * (Note: the constraint is NOT considered in this.)
   */
  Level queryLevel() { return _level; }

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
  Lhs patternStatus() { return _pattern; }

  /**
   * Returns Root.FUNCTION if the root of the left-hand side is a non-theory function symbol,
   * Root.CALC if the root of the left-hand side is a theory symbol, and Root.ANY if the
   * left-hand side does not have a function symbol as root.
   */
  Root rootStatus() { return _rootStatus; }

  /**
   * Returns FreshRight.NONE if all the meta-variables in the right-hand side of the rule also
   * occur in the let-hand side, FreshRight.CVARS if they all occur in the left-hand side of the
   * rule or the constraint, and FreshRight.ANY if there is some meta-variable that does not occur
   * in the left-hand side or the constraint.
   */
  FreshRight rightReplaceablePolicy() { return _fresh; }

  /** Constructor that sets up the minimum value for all properties. */
  RuleRestrictions() {
    _level = Level.FIRSTORDER;
    _theories = false;
    _products = false;
    _pattern = Lhs.PATTERN;
    _rootStatus = Root.FUNCTION;
    _fresh = FreshRight.NONE;
  }

  /** 
   * Constructor that sets up all values in order.  This can only be called from within the trs
   * package.
   */
  RuleRestrictions(Level lvl, Constrained theories, TypeLevel types, Lhs pattern, Root rootstat,
                   FreshRight fresh) {
    _level = lvl;
    _theories = (theories == Constrained.YES);
    _products = (types == TypeLevel.SIMPLEPRODUCTS);
    _pattern = pattern;
    _rootStatus = rootstat;
    _fresh = fresh;
  }

  /** Constructor that sets up the values corresponding to a given rule. */
  RuleRestrictions(Term left, Term right, Term constraint, Collection<Variable> lvars) {
    // level
    if (left.isFirstOrder() && right.isFirstOrder()) _level = Level.FIRSTORDER;
    else if (left.isApplicative() && right.isApplicative()) _level = Level.APPLICATIVE;
    else if (left.isTrueTerm() && right.isTrueTerm()) _level = Level.LAMBDA;
    else _level = Level.META;
    // pattern restriction
    if (left.isPattern()) _pattern = Lhs.PATTERN;
    else if (_level != Level.META) _pattern = Lhs.SEMIPATTERN;
    else if (left.isSemiPattern()) _pattern = Lhs.SEMIPATTERN;
    else _pattern = Lhs.NONPATTERN;
    // root status
    if (!left.isFunctionalTerm()) _rootStatus = Root.ANY;
    else if (left.queryRoot().isTheorySymbol()) _rootStatus = Root.THEORY;
    else _rootStatus = Root.FUNCTION;
    // theories and products
    _theories = false;
    _products = false;
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
    // fresh (meta-)variables
    _fresh = FreshRight.NONE;
    ReplaceableList inleft = left.freeReplaceables();
    ReplaceableList incons = constraint.freeReplaceables();
    for (Replaceable x : right.freeReplaceables()) {
      if (!inleft.contains(x)) {
        if (incons.contains(x)) _fresh = FreshRight.CVARS;
        else { _fresh = FreshRight.ANY; break; }
      }
    }
  }

  /**
   * This checks if all our properties are ≥ those of other.
   * If so, null is returned.
   * If not, a message is returned explaining the problem.
   */
  String checkCoverage(RuleRestrictions other) {
    if (_level.compareTo(other._level) < 0) {
      Map<Level,String> explanation = Map.of(
        Level.FIRSTORDER, "first-order ", Level.APPLICATIVE, "applicative ",
        Level.LAMBDA, "true ", Level.META, "meta-");
      return "rule level is limited to " + explanation.get(_level) + "terms, not " +
        explanation.get(other._level) + "terms";
    }
    if (_rootStatus.compareTo(other._rootStatus) < 0) {
      String original = switch (_rootStatus) {
        case Root.FUNCTION -> "a non-theory function symbol";
        case Root.THEORY -> "a function symbol";
        case Root.ANY -> "MEH THERE IS A BUG IN CHECKCOVERAGE";
      };
      String real = switch (other._rootStatus) {
        case Root.FUNCTION -> "EEK THERE IS A BUG IN CHECKCOVERAGE";
        case Root.THEORY -> "a theory symbol";
        case Root.ANY -> "anything else";
      };
      return "left-hand side should have " + original + " as root, not " + real;
    }
    if (_pattern.compareTo(other._pattern) < 0) {
      Map<Lhs,String> explanation = Map.of(
        Lhs.PATTERN, "pattern", Lhs.SEMIPATTERN, "semi-pattern", Lhs.NONPATTERN, "non-pattern");
      return "left-hand side should be a " + explanation.get(_pattern) + ", not a " +
        explanation.get(other._pattern);
    }
    if (_fresh.compareTo(other._fresh) < 0) {
      return "right-hand side contains a " + (other._level == Level.META ? "meta-" : "") +
        "variable that does not occur in the left-hand side" +
        (_fresh == FreshRight.NONE ? "" : " or the constraint");
    }
    if (!_theories && other._theories) {
      return "use of theory symbols / constraints is not supported";
    }
    if (!_products && other._products) {
      return "use of tuples (or any occurrence of product types) is not supported";
    }
    return null;
  }

  /** This returns if all our properties are ≥ than those of other. */
  boolean covers(RuleRestrictions other) {
    return checkCoverage(other) == null;
  }

  /** This returns the smallest RuleRestrictions class that is ≥ both this and other. */
  RuleRestrictions supremum(RuleRestrictions other) {
    Level maxlevel = _level;
    Root maxroot = _rootStatus;
    Lhs maxpattern = _pattern;
    FreshRight maxfresh = _fresh;
    boolean maxtheories = _theories;
    boolean maxproducts = _products;
    if (other._level.compareTo(maxlevel) > 0) maxlevel = other._level;
    if (other._rootStatus.compareTo(maxroot) > 0) maxroot = other._rootStatus;
    if (other._pattern.compareTo(maxpattern) > 0) maxpattern = other._pattern;
    if (other._fresh.compareTo(maxfresh) > 0) maxfresh = other._fresh;
    if (other._theories) maxtheories = true;
    if (other._products) maxproducts = true;
    return new RuleRestrictions(maxlevel, maxtheories ? Constrained.YES : Constrained.NO,
      maxproducts ? TypeLevel.SIMPLEPRODUCTS : TypeLevel.SIMPLE, maxpattern, maxroot,
      maxfresh);
  }

  /** Used for debugging */
  public String toString() {
    return "{ " + _level + " ; " + _theories + " ; " + _products + " ; " + _pattern + " ; " +
      _rootStatus + " ; " + _fresh + " }";
  };
}

