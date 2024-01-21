/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

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

import java.util.ArrayList;
import java.util.Map;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.IllegalRuleError;
import cora.exceptions.TypingError;
import cora.types.Type;
import cora.types.TypeFactory;
import cora.terms.*;
import cora.smt.TermAnalyser;

/**
 * Rules are the core objects that define the reduction relation in a term rewriting system.  These
 * can be first-order or higher-order, constrained or unconstrained.  They always have the form
 * l → r : φ, although this is viewed as just l → r if there is no constraint.
 */
public class Rule {
  private final Term _left;
  private final Term _right;
  private final Term _constraint;

  /**
   * Creates a rule with the given left- and right-hand side and constraint.
   * To support error checking, a TrsKind is given which the Rule must support.
   */
  Rule(Term left, Term right, Term constraint, TrsKind restriction) {
    _left = left;
    _right = right;
    _constraint = constraint;
    checkRestrictions(restriction);
  }

  /**
   * Creates an unconstrained rule with the given left- and right-hand side.
   * To support error checking, a TrsKind is given which the Rule must support.
   */
  Rule(Term left, Term right, TrsKind restriction) {
    _left = left;
    _right = right;
    _constraint = TheoryFactory.createValue(true);
    checkRestrictions(restriction);
  }

  public Term queryLeftSide() {
    return _left;
  }

  public Term queryRightSide() {
    return _right;
  }

  public Term queryConstraint() {
    return _constraint;
  }

  /**
   * It is not guaranteed in all kinds of TRSs that the left-hand side has a root symbol, so this
   * returns the root symbol if defined, and otherwise null.
   */
  public FunctionSymbol queryRoot() {
    if (_left.isFunctionalTerm()) return _left.queryRoot();
    else return null;
  }

  public Type queryType() {
    return _left.queryType();
  }

  public boolean isFirstOrder() {
    return _left.isFirstOrder() && _right.isFirstOrder();
  }

  public boolean isApplicative() {
    return _left.isApplicative() && _right.isApplicative();
  }

  public boolean isPatternRule() {
    return _left.isPattern() && _left.isFunctionalTerm();
  }

  /**
   * Returns whether the right-hand side has variables or meta-variables not occuring in the left.
   */
  public boolean rightHasFresh() {
    ReplaceableList rlst = _right.freeReplaceables();
    ReplaceableList llst = _left.freeReplaceables();
    for (Replaceable x : rlst) {
      if (!llst.contains(x)) return true;
    }
    return false;
  }

  /**
   * This returns whether the rule is a constrained rule -- which is the case if the constraint
   * is anything other than the value true.
   */
  public boolean isConstrained() {
    Value value = _constraint.toValue();
    if (value == null) return true;
    return !value.getBool();
  }

  /** Gives a string representation of the current rule. */
  public String toString() {
    StringBuilder builder = new StringBuilder();
    Map<Replaceable,String> renaming = _left.getUniqueNaming();
    _left.addToString(builder, renaming);
    builder.append(" → ");
    _right.addToString(builder, renaming);
    if (isConstrained()) {
      builder.append(" | ");
      _constraint.addToString(builder, renaming);
    }
    return builder.toString();
  }

  // ==============================================================================================
  // below here: verifying that the rule satisfies the restrictions it was set up with, and both
  // storing and allowing TRSs to check, the actual restrictions satisfied by the rules

  private boolean _isConstrained; // true if this rule uses theory symbols, a fresh variable in the
                                  // right-hand side, or has a constraint
  private int _constraintLevel;   // the level of the constraint: CONSTRAINTS_FO, CONSTRAINTS_LAMBDA
                                  // or CONSTRAINTS_TRUE

  /**
   * Helper function for the constructor: makes sure that the current rule may occur in a TRS with
   * the given TRS kind, and stores properties about the restrictions that the rule does satisfy.
   */
  private void checkRestrictions(TrsKind restriction) {
    // core requirements that all kinds of TRSs should satisfy; perhaps some parts of these
    // requirements will become optional in the future, but for now, we assume that all rules must
    // satisfy them
    checkNothingNull();
    checkTypesCorrect();
    checkClosed();
    checkLhsFunctional();

    // The checks for the remaining properties differ based on the restrictions from the TrsKind:
    // in some settings restrictions disappear entirely, in others they merely change.  Each of the
    // calls may also cause the properties below to be updated.
    _isConstrained = false;
    _constraintLevel = TrsKind.CONSTRAINTS_FO;
    checkNoFreshCreation(!restriction.rulesUnconstrained());
    if (!checkConstraintEmpty(restriction.rulesUnconstrained())) {
      checkConstraintTheory();
      checkConstraintVariables();
      checkConstraintLevel(restriction.constraintsFirstOrder(),
                           restriction.higherVarsInConstraints());
    }



    // set _isConstrained to true if it wasn't set yet, and any theory symbols are used, and throw
    // an error accordingly if we were supposed to be unconstrained

    // ensure that left-hand side has a non-theory symbol at the root if required
    // otherwise, still ensure that left-hand side is not a theory term

    // check level, if given

    // check that left-hand side is a functional term, if required
    // otherwise, check that left-hand side is not a variable, if required

    // check that no meta-variables are used, unless allowed
    // check that left-hand sides are patterns, unless allowed
    // check that terms are product-free unless allowed
  }

  /** Checks that no parts of a rule are null. */
  private void checkNothingNull() {
    if (_left == null) throw new NullInitialisationError("Rule", "left-hand side");
    if (_right == null) throw new NullInitialisationError("Rule", "right-hand side");
    if (_constraint == null) throw new NullInitialisationError("Rule", "constraints");
  }

  /** Checks that both sides of a rule have the same type, and the constraint has type Bool */
  private void checkTypesCorrect() {
    if (!_left.queryType().equals(_right.queryType())) {
      throw new TypingError("Rule", "checkTypesCorrect", "right-hand side",
                            _right.queryType().toString(), _left.queryType().toString());
    }
    Type t = _constraint.queryType();
    if (!t.equals(TypeFactory.boolSort) || !t.isTheoryType()) {
      throw new IllegalRuleError("Rule", "constraint [" + _constraint.toString() + "] does not " +
        "have the theory sort Bool (it has type " + t.toString() + ").");
    }
  }

  /** Checks that both sides are closed: no binder variables occur. */
  private void checkClosed() {
    String problem = null;
    if (!_left.isClosed()) problem = "_left";
    else if (!_right.isClosed()) problem = "_right";
    if (problem != null) {
      throw new IllegalRuleError("Rule", problem + "-hand side of rule [" + toString() + "] is " +
        "not closed (that is, freely contains a binder-variable).");
    }
  }
  
  /** Checks that the left-hand side of the rule is a functional term. */
  private void checkLhsFunctional() {
    if (!_left.isFunctionalTerm()) {
      throw new IllegalRuleError("Rule", "rule [" + toString() + "] has a left-hand side that " +
        "is not a functional term.");
    }
  }

  /**
   * Checks that no variables or meta-variables occur on the right-hand side of a rule that don't
   * occur on the left.
   * If theories is true, then one exception is allowed: variables of a theory sort are allowed to
   * occur fresh.  In this case, we do store that the current rule is a constrained rule.
   */
  private void checkNoFreshCreation(boolean theories) {
    ReplaceableList lvars = _left.freeReplaceables();
    ReplaceableList rvars = _right.freeReplaceables();
    for (Replaceable x : rvars) {
      if (!lvars.contains(x)) {
        if (!theories || x.queryReplaceableKind() == Replaceable.KIND_METAVAR) {
          String kind = (x.queryReplaceableKind() == Replaceable.KIND_METAVAR ? "meta-" : "");
          throw new IllegalRuleError("Rule", "_right-hand side of rule [" + toString() + "] " +
            "contains " + kind + "variable " + x.toString() + " which does not occur on the _left.");
        }
        else if (!x.queryType().isBaseType() || !x.queryType().isTheoryType()) {
          throw new IllegalRuleError("Rule", "_right-hand side of rule [" + toString() + "] " +
            "contains fresh variable " + x.toString() + " of type " + x.queryType().toString() +
            ", which is not a theory sort.");
        }
        else _isConstrained = true;
      }
    }
  }

  /**
   * Checks if the constraint is T, and if so, returns true.  If not, then _consstrained is set to
   * true, an IllegalRuleError is thrown if the parameter ruleShouldBeUnconstrained is set to true,
   * and otherwise false is returned.
   */
  private boolean checkConstraintEmpty(boolean ruleShouldBeUnconstrained) {
    if (_constraint.isValue() && _constraint.toValue().getBool()) return true;
    _isConstrained = true;
    if (ruleShouldBeUnconstrained) {
      throw new IllegalRuleError("Rule", "Rule [" + toString() + "] has a constraint, which " +
        "is not permitted in this kind of TRS.");
    }
    return false;
  }

  /** Checks that the constraint is a theory term. */
  private void checkConstraintTheory() {
    if (!_constraint.isTheoryTerm()) {
      throw new IllegalRuleError("Rule", "constraint [" + _constraint.toString() + "] is not a " +
        "theory term.");
    }
  }

  /**
   * Check that the constraint has no meta-variables, and all free variables are non-binder
   * variables of a theory type.
   */
  private void checkConstraintVariables() {
    ReplaceableList cvars = _constraint.freeReplaceables();
    for (Replaceable x : cvars) {
      if (x.queryReplaceableKind() == Replaceable.KIND_BINDER) {
        throw new IllegalRuleError("Rule", "constraint [" + _constraint.toString() + "] contains " +
          "a binder variable " + x.toString() + ".");
      }
      if (x.queryReplaceableKind() == Replaceable.KIND_METAVAR) {
        throw new IllegalRuleError("Rule", "constraint [" + _constraint.toString() + "] contains " +
          "a meta-variable " + x.toString() + "; only true terms are allowed in constraints.");
      }
      if (!x.queryType().isTheoryType()) {
        throw new IllegalRuleError("Rule", "constraint [" + _constraint.toString() + "] contains " +
          "a variable " + x.toString() + " of type " + x.queryType().toString() + "; only " +
          "variables of a theory type are allowed to occur in a constraint.");
      }
    }
  }

  /** Determines which higher-order aspects -- if any -- the constraint has. */
  private void checkConstraintLevel(boolean shouldBeFo, boolean higherVarsAllowed) {
    if (_constraint.isFirstOrder()) {
      _constraintLevel = TrsKind.CONSTRAINTS_FO;
      return;
    }
    if (shouldBeFo) {
      throw new IllegalRuleError("Rule", "constraint [" + _constraint.toString() + "] is not " +
        "first-order.");
    }
    _constraintLevel = TrsKind.CONSTRAINTS_LAMBDA;
    for (Variable x : _constraint.vars()) {
      if (x.queryType().queryTypeOrder() != 0) {
        _constraintLevel = TrsKind.CONSTRAINTS_TRUE;
        if (higherVarsAllowed) return;
        throw new IllegalRuleError("Rule", "constraint [" + _constraint.toString() + "] uses a " +
          "higher-order variable " + x.toString() + ".");
      }
    }
  }







}

