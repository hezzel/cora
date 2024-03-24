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

import com.google.common.collect.ImmutableList;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import charlie.exceptions.IllegalRuleError;
import charlie.exceptions.NullInitialisationError;
import charlie.exceptions.TypingError;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.types.TypePrinter;
import charlie.terms.*;
import charlie.trs.TrsProperties.*;

/**
 * Rules are the core objects that define the reduction relation in a term rewriting system.  These
 * can be first-order or higher-order, constrained or unconstrained.  They always have the form
 * l → r : φ, although this is viewed as just l → r if there is no constraint.
 */
public class Rule {
  private final Term _left;
  private final Term _right;
  private final Term _constraint;
  private ImmutableList<Variable> _lvars;
  private RuleRestrictions _properties;

  /**
   * Creates a rule with the given left- and right-hand side and constraint.
   * The constructor verifies that the rule is set up correctly, and stores its properties for
   * later querying.
   */
  Rule(Term left, Term right, Term constraint) {
    _left = left;
    _right = right;
    _constraint = constraint;
    checkCorrectness(); // this goes first, because the null check is in checkCorrectness
    calculateLVars();
    _properties = new RuleRestrictions(_left, _right, _constraint, _lvars);
  }

  /**
   * Creates an unconstrained rule with the given left- and right-hand side, but no constraint.
   * The constructor verifies that the rule is set up correctly, and stores its properties for
   * later querying.
   */
  Rule(Term left, Term right) {
    _left = left;
    _right = right;
    _constraint = TheoryFactory.createValue(true);
    checkCorrectness();
    calculateLVars();
    _properties = new RuleRestrictions(_left, _right, _constraint, _lvars);
  }

  public Term queryLeftSide() {
    return _left;
  }

  public Term queryRightSide() {
    return _right;
  }

  /** Returns the constraint.  In an unconstrained rule, this is just TRUE. */
  public Term queryConstraint() {
    return _constraint;
  }

  public ImmutableList<Variable> queryLVars() {
    return _lvars;
  }

  /** Only for internal use within the trs package. */
  RuleRestrictions queryProperties() {
    return _properties;
  }

  /**
   * It is not guaranteed in all kinds of TRSs that the left-hand side has a root symbol, so this
   * returns the root symbol if defined, and otherwise null.
   */
  public FunctionSymbol queryRoot() {
    if (_left.isFunctionalTerm()) return _left.queryRoot();
    else return null;
  }

  /** Returns the type of left- and right-hand side of this rule. */
  public Type queryType() {
    return _left.queryType();
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

  /** This returns whether both left- and right-hand side of the rule are first-order. */
  public boolean isFirstOrder() {
    return _properties.queryLevel() == Level.FIRSTORDER;
  }

  /** This returns whether both left- and right-hand side of the rule are applicative. */
  public boolean isApplicative() {
    return _properties.queryLevel().compareTo(Level.APPLICATIVE) <= 0;
  }

  /** This returns whether both left- and right-hand side of the rule are true terms. */
  public boolean isMetaFree() {
    return _properties.queryLevel().compareTo(Level.LAMBDA) <= 0;
  }

  /** This returns whether the rule has a pattern as its left-hand side. */
  public boolean isPatternRule() {
    return _properties.patternStatus() == Lhs.PATTERN;
  }
  
  /** This returns whether the rule has a semi-pattern as its left-hand side. */
  public boolean isSemiPatternRule() {
    return _properties.patternStatus().compareTo(Lhs.SEMIPATTERN) <= 0;
  }
  
  /** This returns whether the left-hand side has a root that is a (non-theory) function symbol. */
  public boolean queryTermFunctionRoot() {
    return _properties.rootStatus() == Root.FUNCTION;
  }

  /** Returns whether the left-hand side has a root that is a (possibly theory) function symbol. */
  public boolean queryFunctionRoot() {
    return _properties.rootStatus().compareTo(Root.THEORY) <= 0;
  }

  /** Gives a string representation of the current rule (debug functionality). */
  public String toString() {
    StringBuilder builder = new StringBuilder();
    TermPrinter printer = new TermPrinter(new TypePrinter(), Set.of());
    TermPrinter.Renaming renaming = printer.generateUniqueNaming(_left, _right, _constraint);
    printer.print(_left, renaming, builder);
    builder.append(" → ");
    printer.print(_right, renaming, builder);
    if (isConstrained()) {
      builder.append(" | ");
      printer.print(_constraint, renaming, builder);
    }
    return builder.toString();
  }

  // ============================== correctness checking starts here ==============================

   /**
   * Helper function for the constructor: this checks that the rule is properly set up, e.g., no
   * null components, left- and right-hand side have the same type, and both sides are closed.
   * The checks that MVars(r) ⊆ MVars(l) and MVars(φ) = ø are postponed to calculateLVars, where
   * they are combined with checks on the free variables of non-theory type.
   */
  private void checkCorrectness() {
    checkNothingNull();
    checkTypesCorrect();
    checkLeftClosed();    // we'll check the right and the constraint separately
    checkLeftNotTheory();
    checkConstraintTheory();
    checkConstraintFirstOrder();
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
      throw new IllegalRuleError("constraint [" + _constraint.toString() + "] does not " +
        "have the theory sort Bool (it has type " + t.toString() + ").");
    }
  }

  /** Checks that both sides are closed: no binder variables occur. */
  private void checkLeftClosed() {
    if (!_left.isClosed()) { 
      throw new IllegalRuleError("left-hand side of rule [" + toString() + "] is not closed " +
        "(that is, freely contains a binder-variable).");
    }
  }

  /** Checks that the left-hand side is not a theory term. */
  private void checkLeftNotTheory() {
    if (_left.isTheoryTerm()) {
      throw new IllegalRuleError("left-hand side of rule [" + toString() + "] is a theory term!");
    }
  }

  /** Checks that the constraint is a theory term. */
  private void checkConstraintTheory() {
    if (!_constraint.isTheoryTerm()) {
      throw new IllegalRuleError("constraint [" + _constraint.toString() + "] is not a theory " +
        "term.");
    }
  }

  /** Checks that the constraint is a first-order term. */
  private void checkConstraintFirstOrder() {
    if (!_constraint.isFirstOrder()) {
      throw new IllegalRuleError("constraint [" + _constraint.toString() + "] is not first-order.");
    }
  }

 /**
   * Helper function for the constructor: calculates the variables (and meta-variables) that occur
   * in the constraint and fresh in the right-hand side, and throws an IllegalRuleError if they are
   * anything but non-binder variables of theory sort.
   */
  private void calculateLVars() {
    ReplaceableList leftvars = _left.freeReplaceables();
    ReplaceableList rightvars = _right.freeReplaceables();
    ImmutableList.Builder<Variable> builder = ImmutableList.<Variable>builder();
    TreeSet<Variable> sofar = new TreeSet<Variable>();
    for (Replaceable x : rightvars) {
      if (leftvars.contains(x)) continue;
      switch (x.queryReplaceableKind()) {
        case Replaceable.KIND_METAVAR:
          throw new IllegalRuleError("right-hand side of rule [" + toString() + "] contains " +
            "meta-variable " + x.toString() + " which does not occur on the left.");
        case Replaceable.KIND_BINDER:
          throw new IllegalRuleError("right-hand side of rule [" + toString() + "] introduces " +
            "a fresh binder variable " + x.toString() + " (so is not closed).");
        case Replaceable.KIND_BASEVAR:
          if (x.queryType().isBaseType() && x.queryType().isTheoryType()) {
            Variable y = (Variable)x;
            if (!sofar.contains(y)) { sofar.add(y); builder.add(y); }
          }
          else {
            throw new IllegalRuleError("right-hand side of rule [" + toString() + "] contains " +
              "variable " + x.queryName() + " of type " + x.queryType().toString() + " which does " +
              "not occur on the left; only variables of theory sorts may occur fresh (and that " +
              "only in some kinds of TRSs).");
          }
          break;
        default: throw new Error("Exhausted switch for queryReplaceableKind");
      }
    }

    // at this point we already checked that the constraint is first-order, so we're only dealing
    // with non-binder variables
    for (Variable y : _constraint.vars()) {
      if (y.queryType().isBaseType() && y.queryType().isTheoryType()) {
        if (!sofar.contains(y)) { sofar.add(y); builder.add(y); }
      }
      else {
        throw new IllegalRuleError("constraint of rule [" + toString() + "] contains variable " +
          y.queryName() + " of type " + y.queryType().toString() + " which is not a theory sort.");
      }
    }
    
    _lvars = builder.build();
  }
}

