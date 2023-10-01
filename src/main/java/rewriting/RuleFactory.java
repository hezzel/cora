/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rewriting;

import cora.exceptions.IllegalRuleError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.TypingError;
import cora.types.Type;
import cora.types.TypeFactory;
import cora.terms.Term;
import cora.terms.Replaceable;
import cora.terms.ReplaceableList;

public class RuleFactory {
  /** Prints a rule with the given left and right hand side, for use in error messages. */
  private static String toString(Term left, Term right) {
    return left.toString() + " → " + right.toString();
  }

  /**
   * Does the checks needed for all kinds of rules, and throws an appropriate erorr if the checks
   * are not satisfied.
   */
  private static void doBasicChecks(Term left, Term right) {
    // neither term is null
    if (left == null) throw new NullInitialisationError("Rule", "left-hand side");
    if (right == null) throw new NullInitialisationError("Rule", "right-hand side");
    // both sides should have the same type
    if (!left.queryType().equals(right.queryType())) {
      throw new TypingError("Rule", "constructor", "right-hand side", right.queryType().toString(),
                            left.queryType().toString());
    }
    // no variables or meta-variables should occur on the right that don't also occur on the left
    ReplaceableList lvars = left.freeReplaceables();
    ReplaceableList rvars = right.freeReplaceables();
    for (Replaceable x : rvars) {
      if (!lvars.contains(x)) {
        String kind = (x.queryReplaceableKind() == Replaceable.KIND_METAVAR ? "meta-" : "");
        throw new IllegalRuleError("Rule", "right-hand side of rule [" + toString(left, right) +
          "] contains " + kind + "variable " + x.toString() + " which does not occur on the left.");
      }
    }
    // both sides should be closed; this is automatic if left is, since all variables occurring
    // free on the right are also free on the left
    if (!left.isClosed()) {
      throw new IllegalRuleError("Rule", "left-hand side of rule [" + toString(left, right) +
        "] is not closed (that is, freely contains a binder-variable).");
    }
  }

  /** 
   * Does the checks for the simple forms of constraints we currently support.
   */
  private static void doConstraintChecks(Term left, Term constraint) {
    // constraints have type Bool
    Type t = constraint.queryType();
    if (!t.equals(TypeFactory.boolSort) || !t.isTheoryType()) {
      throw new IllegalRuleError("Rule", "constraint [" + constraint.toString() + "] does not " +
        "have the theory sort Bool (it has type " + t.toString() + ").");
    }
    // constraints are theory terms
    if (!constraint.isTheoryTerm()) {
      throw new IllegalRuleError("Rule", "constraint [" + constraint.toString() + "] is not a " +
        "theory term.");
    }
    // all variables in the constraint are non-binder variables of a theory sort
    ReplaceableList cvars = constraint.freeReplaceables();
    for (Replaceable x : cvars) {
      if (x.queryReplaceableKind() == Replaceable.KIND_BINDER) {
        throw new IllegalRuleError("Rule", "constraint [" + constraint.toString() + "] contains " +
          "a binder variable " + x.toString() + ".");
      }
      if (x.queryReplaceableKind() == Replaceable.KIND_METAVAR) {
        throw new IllegalRuleError("Rule", "constraint [" + constraint.toString() + "] contains " +
          "a meta-variable " + x.toString() + "; only properly first-order constraints are " +
          "allowd.");
      }
      t = x.queryType();
      if (!x.queryType().isBaseType() || !x.queryType().isTheoryType()) {
        throw new IllegalRuleError("Rule", "constraint [" + constraint.toString() + "] contains " +
          "a variable " + x.toString() + " of type " + t.toString() + "; only variables of " +
          "theory sort are allowed to occur in a constraint.");
      }
    }
    // constraints are first-order (we already covered most alternatives, but some still remain)
    if (!constraint.isFirstOrder()) {
      throw new IllegalRuleError("Rule", "constraint [" + constraint.toString() + "] is not " +
        "first-order.");
    }

    // for now, we require that no variables or meta-variables occur in the constraint that do not
    // also coccur on the left
    ReplaceableList lvars = left.freeReplaceables();
    for (Replaceable x : cvars) {
      if (!lvars.contains(x)) {
        throw new IllegalRuleError("Rule", "constraint [" + constraint + "] contains variable " +
          x.toString() + " which does not occur in the rule's left-hand side.  This is not yet " +
          "supported.");
      }
    }
  }

  /**
   * Create a constrained first-order rule.
   * If the rule is poorly formed or not first-order, an IllegalRuleError is thrown.
   * (It is well-formed if: FV(r) ⊆ FV(l) and both sides have the same sort.)
   */
  public static Rule createFirstOrderRule(Term left, Term right, Term constraint) {
    // do the checks that apply to everything, not just first-order rules
    doBasicChecks(left, right);
    // and the ones that should apply to the constraint
    if (constraint != null) doConstraintChecks(left, constraint);
    // both sides need to be first-order
    if (!left.isFirstOrder() || !right.isFirstOrder()) {
      throw new IllegalRuleError("RuleFactory::createFirstOrderRule", "terms in rule [" +
        toString(left, right) + "] are not first-order.");
    }   
    // the left-hand side should have the form f(...)
    if (!left.isFunctionalTerm()) {
        throw new IllegalRuleError("RuleFactory::createFirstOrderRule", "illegal rule [" +
          toString(left, right) + "] with a variable as the left-hand side.");
    }
    if (constraint == null) return new Rule(left, right);
    else return new Rule(left, right, constraint);
  }

  /**
   * Create a first-order rule.
   * If the rule is poorly formed or not first-order, an IllegalRuleError is thrown.
   * (It is well-formed if: FV(r) ⊆ FV(l) and both sides have the same sort.)
   */
  public static Rule createFirstOrderRule(Term left, Term right) {
    return createFirstOrderRule(left, right, null);
  }

  /**
   * Create an applicative higher-order rule.
   * If the rule is poorly formed or not applicative, an IllegalRuleError is thrown.
   * (It is well-formed if: FV(r) ⊆ FV(l) and both sides have the same type.)
   */
  public static Rule createApplicativeRule(Term left, Term right) {
    // do the checks that apply to everything, not just applicative rules
    doBasicChecks(left, right);
    // both sides need to be applicative
    if (!left.isApplicative() || !right.isApplicative()) {
      throw new IllegalRuleError("RuleFactory::createApplicativeRule", "terms in rule [" +
        toString(left, right) + " are not applicative.");
    }
    return new Rule(left, right);
  }

  /**
   * Create a meta-variable-free higher-order rule, so where both sides are true terms.
   * If the rule is poorly formed or has meta-applications, an IllegalRuleError is thrown.
   * (It is well-formed if: FV(r) ⊆ FV(l) and both sides have the same sort.)
   */
  public static Rule createCFSRule(Term left, Term right) {
    // do the checks that apply to everything
    doBasicChecks(left, right);
    // both sides need to be true terms
    if (!left.isTrueTerm() || !right.isTrueTerm()) {
      throw new IllegalRuleError("RuleFactory::createCFSRule", "meta-terms in rule [" +
        toString(left, right) + " are not true terms.");
    }
    return new Rule(left, right);
  }

  /**
   * Create a pattern rule, so where the left-hand sides are patterns of the form
   * f(l1,...,ln).  If the rule is poorly formed (i.e., the right-hand side contains a
   * meta-variable not occurring on the left, the rule is not closed, the left-hand side has the
   * wrong shape, or the sides do not have the same sort), an IllegalRuleError is thrown.
   */
  public static Rule createPatternRule(Term left, Term right) {
    // do the checks that apply to everything
    doBasicChecks(left, right);
    // the left-hand side needs to be a pattern
    if (!left.isPattern()) {
      throw new IllegalRuleError("RuleFactory::createPatternRule", "left-hand side of rule [" +
        toString(left, right) + " is not a pattern.");
    }
    // the left-hand side should have the form f(...)
    if (!left.isFunctionalTerm()) {
        throw new IllegalRuleError("RuleFactory::createPatternRule", "illegal rule [" +
          toString(left, right) + "], where the left-hand side does not have a fucntion symbol " +
          "as the root.");
    }
    return new Rule(left, right);
  }

  /**
   * Creates an AMS rule without limitations other than well-formedness: FMV(r) ⊆ FMV(l), both
   * sides should have the same sort, and both sides should be closed.
   */
  public static Rule createRule(Term left, Term right) {
    doBasicChecks(left, right);
    return new Rule(left, right);
  }
}

