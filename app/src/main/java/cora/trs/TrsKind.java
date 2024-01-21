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

/**
 * The TrsKind class tracks properties of a TRS.
 *
 * There are three kinds of properties.  The first kind, consisting of three properties, consider
 * the kind of terms this TrsKind is expected to admit:
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
 * The second kind are the same as the first, but limited to the rules:
 * - level (of the terms in left- or right-hand sides of the rules)
 * - theories (whether the rules can use theories or fresh variables on the right, and may have a
 *   constraint in the first place)
 * - tuples (whether the rules may have subterms with a type containing products)
 * By default, the rules may have the same level, theories and tuples support as arbitrary terms in
 * the TRS.  They certainly cannot have more.  However, it is possible for a TRS to have rules
 * which all satisfy a lower level -- for example, TRSs with applicative rules, but where lambda is
 * allowed in term formation.
 *
 * The third kind of properties are additional restrictions that rules satisfy.  These can be:
 * - left-hand sides of rules are patterns or not
 * - rules may use meta-variables or not (this is only relevant for LVL_LAMBDA)
 * - rules are allowed to have a theory symbol as root symbol or not
 * - constraints are first-order, allow lambda but not higher-order variables,
 *   or may be any true term (meta-variables are never allowed)
 * By default, these are all assumed at the minimal level (left-hand sides are patterns, rules may
 * not use meta-variables, and constraints are first-order), so exceptions to these default
 * assumptions must be explicitly supplied.
 *
 * Every TrsKind is immutable.
 *
 * Changes to TrsKind should be reflected in Rule and TRS as well.
 */
public class TrsKind {
  public static final int LVL_FIRSTORDER            = 11;
  public static final int LVL_APPLICATIVE           = 12;
  public static final int LVL_LAMBDA                = 13;
  public static final int THEORIES_NONE             = 21;
  public static final int THEORIES_YES              = 22;
  public static final int PRODUCTS_DISALLOWED       = 31;
  public static final int PRODUCTS_ALLOWED          = 32;
  public static final int RULES_LVL_FIRSTORDER      = 41;
  public static final int RULES_LVL_APPLICATIVE     = 42;
  public static final int RULES_LVL_LAMBDA          = 43;
  public static final int RULES_THEORIES_NONE       = 51;
  public static final int RULES_THEORIES_YES        = 52;
  public static final int RULES_PRODUCTS_DISALLOWED = 61;
  public static final int RULES_PRODUCTS_ALLOWED    = 62;
  public static final int LHS_PATTERNS              = 71;
  public static final int LHS_NO_PATTERNS           = 72;
  public static final int META_NO                   = 81;
  public static final int META_YES                  = 82;
  public static final int CONSTRAINTS_FO            = 91;
  public static final int CONSTRAINTS_LAMBDA        = 92;
  public static final int CONSTRAINTS_TRUE          = 93;
  public static final int ROOT_NOT_THEORY           = 101;
  public static final int ROOT_THEORY_ALLOWED       = 102;

  // the difference between "level" and "rules level", "theories" and "rules theories", and
  // "products" and "rules products"
  private static final int RULESDIF = RULES_LVL_FIRSTORDER - LVL_FIRSTORDER;

  private int _level;
  private int _theories;
  private int _tuples;
  private int _rulesLevel;
  private int _rulesTheories;
  private int _rulesTuples;
  private int _patterns;
  private int _meta;
  private int _constraintsLevel;
  private int _rootTheory;

  /** Returns whether terms are necessarily first-order. */
  public boolean termsFirstOrder() { return _level == LVL_FIRSTORDER; }

  /** Returns whether terms necessarily applicative (lambda-free). */
  public boolean termsApplicative() { return _level <= LVL_APPLICATIVE; }

  /** Returns whether terms using theory symbols are allowed to occur. */
  public boolean theoriesIncluded() { return _theories == THEORIES_YES; }

  /** Returns whether terms using product types are allowed to occur. */
  public boolean productTypesAllowed() { return _tuples == PRODUCTS_ALLOWED; }

  /** Returns whether rules are restricted to first-order lhs and rhs. */
  public boolean rulesFirstOrder() { return _rulesLevel == RULES_LVL_FIRSTORDER; }

  /** Returns whether rules are restricted to lambda-free lhs and rhs. */
  public boolean rulesApplicative() { return _rulesLevel <= RULES_LVL_APPLICATIVE; }

  /** Returns true if rules are blocked from using theory symbols, or logical constraints. */
  public boolean rulesUnconstrained() { return _rulesTheories == RULES_THEORIES_NONE; }

  /** Returns true if rules must be built without the use of product types. */
  public boolean rulesTupleFree() { return _rulesTuples == RULES_PRODUCTS_DISALLOWED; }

  /** Returns true if rules must have patterns as their left-hand side. */
  public boolean patternRestriction() { return _patterns == LHS_PATTERNS; }

  /** Returns true if rules are allowed to use meta-application. */
  public boolean rulesUsingMeta() { return _meta == META_YES; }

  /** Returns true if constraints in rules must be first-order. */
  public boolean constraintsFirstOrder() { return _constraintsLevel == CONSTRAINTS_FO; }

  /** Returns true if constraints are allowed to use lambdas. */
  public boolean lambdaInConstraints() { return _constraintsLevel >= CONSTRAINTS_LAMBDA; }

  /** Returns true if higher-order variables are allowed to occur in constraints. */
  public boolean higherVarsInConstraints() { return _constraintsLevel >= CONSTRAINTS_TRUE; }

  /** Returns true if root symbols of left-hand sides may be calculation symbols. */
  public boolean rootMustBeNonTheory() { return _rootTheory == ROOT_NOT_THEORY; }

  /**
   * Sets up the TrsKind with the given properties, which should be the public constants in TrsKind.
   *
   * It is not required to prove all properties.  Properties that are not given are handled as
   * follows:
   * - for the terms properties, and additional restrictionson rules, the lowest possible value is
   *   assumed; e.g., first-order, no theories or tuples, pattern restriction, etc.
   * - for the rule limitation of the term properties (level, constraints and products), if they are
   *   not given they are set to the same value as the term properties; e.g., if LVL_APPLICATIVE is
   *   supplied but none of the RULES_LVL_... properties, then RULES_LVL_APPLICATIVE is assumed.
   *
   * If multiple properties of the same category are given (e.g., both RULES_LVL_FIRSTORDER and
   * RULES_LVL_APPLICATIVE), an IllegalArgumentError is thrown; this also happens for an unknown
   * argument, or if the requirements on rules are more permissive than those on terms.
   */
  TrsKind(int[] properties) {
    _level = _theories = _tuples = _rulesLevel = _rulesTheories = _rulesTuples = _patterns
           = _meta = _constraintsLevel = _rootTheory = 0;

    for (int prop : properties) setProperty(prop);

    if (_level == 0)            _level = LVL_FIRSTORDER;
    if (_theories == 0)         _theories = THEORIES_NONE;
    if (_tuples == 0)           _tuples = PRODUCTS_DISALLOWED;
    if (_rulesLevel == 0)       _rulesLevel = _level + RULESDIF;
    if (_rulesTheories == 0)    _rulesTheories = _theories + RULESDIF;
    if (_rulesTuples == 0)      _rulesTuples = _tuples + RULESDIF;
    if (_patterns == 0)         _patterns = LHS_PATTERNS;
    if (_meta == 0)             _meta = META_NO;
    if (_constraintsLevel == 0) _constraintsLevel = CONSTRAINTS_FO;
    if (_rootTheory == 0)       _rootTheory = ROOT_NOT_THEORY;
    
    checkConsistency();
  }

  /**
   * Sets up the TrsKind with the given properties, where any properties not given should
   * default to the corresponding value in defaultKind.
   * Note that if you update a term restriction using this, you may also need to update the
   * corresponding rules restriction to avoid an IllegalArgumentError; this is not done
   * automatically.
   */
  TrsKind(TrsKind defaultKind, int[] updates) {
    _level = _theories = _tuples = _rulesLevel = _rulesTheories = _rulesTuples = _patterns
           = _meta = _constraintsLevel = _rootTheory = 0;

    for (int prop : updates) setProperty(prop);

    if (_level == 0)            _level = defaultKind._level;
    if (_theories == 0)         _theories = defaultKind._theories;
    if (_tuples == 0)           _tuples = defaultKind._tuples;
    if (_rulesLevel == 0)       _rulesLevel = defaultKind._rulesLevel;
    if (_rulesTheories == 0)    _rulesTheories = defaultKind._rulesTheories;
    if (_rulesTuples == 0)      _rulesTuples = defaultKind._rulesTuples;
    if (_patterns == 0)         _patterns = defaultKind._patterns;
    if (_meta == 0)             _meta = defaultKind._meta;
    if (_constraintsLevel == 0) _constraintsLevel = defaultKind._constraintsLevel;
    if (_rootTheory == 0)       _rootTheory = defaultKind._rootTheory;
    
    checkConsistency();
  }

  /** Helper function for the constructor: this function sets the required property. */
  private void setProperty(int prop) {
    switch (prop) {
      case LVL_FIRSTORDER, LVL_APPLICATIVE, LVL_LAMBDA:
        _level = duplicationCheck(_level, prop, "TRS level");
        break;
      case THEORIES_NONE, THEORIES_YES:
        _theories = duplicationCheck(_theories, prop, "theory support");
        break;
      case PRODUCTS_DISALLOWED, PRODUCTS_ALLOWED:
        _tuples = duplicationCheck(_tuples, prop, "allowing product types and tuples");
        break;
      case RULES_LVL_FIRSTORDER, RULES_LVL_APPLICATIVE, RULES_LVL_LAMBDA:
        _rulesLevel = duplicationCheck(_rulesLevel, prop, "rules level");
        break;
      case RULES_THEORIES_NONE, RULES_THEORIES_YES:
        _rulesTheories = duplicationCheck(_rulesTheories, prop, "theory support in rules");
        break;
      case RULES_PRODUCTS_DISALLOWED, RULES_PRODUCTS_ALLOWED:
        _rulesTuples = duplicationCheck(_rulesTuples, prop, "allowing product types in rules");
        break;
      case LHS_PATTERNS, LHS_NO_PATTERNS:
        _patterns = duplicationCheck(_patterns, prop, "pattern requirement");
        break;
      case META_NO, META_YES:
        _meta = duplicationCheck(_meta, prop, "meta-variable use");
        break;
      case CONSTRAINTS_FO, CONSTRAINTS_LAMBDA, CONSTRAINTS_TRUE:
        _constraintsLevel = duplicationCheck(_constraintsLevel, prop, "constraints level");
        break;
      case ROOT_NOT_THEORY, ROOT_THEORY_ALLOWED:
        _rootTheory = duplicationCheck(_rootTheory, prop, "root calculation symbol allowance");
        break;
      default:
        throw new IllegalArgumentError("TrsKind", "constructor", "unknown property value " + prop);
    }
  }

  /**
   * Helper function for the constructor: if value == 0 it returns property, otherwise it throws an
   * IllegalArgumentError indicating thta the property is getting set twice.
   */
  private int duplicationCheck(int value, int property, String description) {
    if (value == 0) return property;
    throw new IllegalArgumentError("TrsKind", "constructor", "duplicate value for " + description +
      " (" + property + ")");
  }

  /** This function checks the consistency of the settings for the various properties. */
  private void checkConsistency() {
    if (_rulesLevel > _level + RULESDIF) {
      throw new IllegalArgumentError("TrsKind", "constructor", "rules level (" + _rulesLevel +
        ") larger than TRS level (" + _level + ")");
    }
    if (_rulesTheories > _theories + RULESDIF) {
      throw new IllegalArgumentError("TrsKind", "constructor", "theories supported in rules " +
        "but not in terms!");
    }
    if (_rulesTuples > _tuples + RULESDIF) {
      throw new IllegalArgumentError("TrsKind", "constructor", "tuples and product types " +
        "supported in rules but not in terms!");
    }
    if (_patterns > LHS_PATTERNS && _rulesLevel == RULES_LVL_FIRSTORDER) {
      throw new IllegalArgumentError("TrsKind", "constructor", "cannot have non-patterns in a " +
        "first-order TRS!");
    }
    if (_constraintsLevel > CONSTRAINTS_FO && _rulesTheories == RULES_THEORIES_NONE) {
      throw new IllegalArgumentError("TrsKind", "constructor", "cannot set higher-order " +
        "constraints when rules don't even use constraints!");
    }
    if (_rootTheory > ROOT_NOT_THEORY && _rootTheory == RULES_THEORIES_NONE) {
      throw new IllegalArgumentError("TrsKind", "constructor", "cannot allow rule root to be a " +
        "theory symbol when theory symbols aren't even allowed in rules!");
    }
  }
}

