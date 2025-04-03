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
import java.util.Set;
import java.util.TreeSet;
import java.util.LinkedList;
import java.util.Collections;
import charlie.exceptions.IllegalRuleException;
import charlie.exceptions.NullStorageException;
import charlie.exceptions.TypingException;
import charlie.exceptions.UnexpectedPatternException;
import charlie.types.Type;
import charlie.types.TypeFactory;
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
  private final Set<Variable> _lvars;
  private Set<Variable> _tvars;
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
    checkCorrectness();
    _lvars = Collections.unmodifiableSet(constraint.vars().toSet());
    _tvars = null;
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
    _lvars = Set.of();
    _tvars = null;
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

  /**
   * Returns an UNMODIFIABLE set containing the variables that must be instantiated by a value.
   * These are exactly the variables in the constraint.
   */
  public Set<Variable> queryLVars() {
    return _lvars;
  }

  /**
   * Returns an UNMODIFIABLE set containing the variables that occur both in the constraint, and in
   * left or right (or both).  These are the variables that play a role both at the term level and
   * at the theory level.
   */
  public Set<Variable> queryTVars() {
    // as a small optimisation, we only compute this if we actually need it
    if (_tvars == null) {
      _tvars = new TreeSet<Variable>();
      for (Variable x : _constraint.vars()) {
        if (_left.freeReplaceables().contains(x) || _right.freeReplaceables().contains(x)) {
          _tvars.add(x);
        }
      }
      _tvars = Collections.unmodifiableSet(_tvars);
    }
    return _tvars;
  }

  /**
   * Returns a set with all replaceables occurring in the current rule.  This is a modifiable set;
   * changing it will not affect the Rule.
   */
  public Set<Replaceable> queryAllReplaceables() {
    Set<Replaceable> ret = new TreeSet<Replaceable>();
    for (Replaceable x : _left.freeReplaceables()) ret.add(x);
    for (Replaceable x : _constraint.freeReplaceables()) ret.add(x);
    if (_properties.rightReplaceablePolicy() == TrsProperties.FreshRight.ANY) {
      for (Replaceable x : _right.freeReplaceables()) ret.add(x);
    }
    return ret;
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

  /** This returns whether the left-hand side of the rule is linear. */
  public boolean isLeftLinear() {
    return _left.isLinear();
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
    TermPrinter printer = new TermPrinter(Set.of());
    Renaming renaming = printer.generateUniqueNaming(_left, _right, _constraint);
    printer.print(_left, renaming, builder);
    builder.append(" → ");
    printer.print(_right, renaming, builder);
    if (isConstrained()) {
      builder.append(" | ");
      printer.print(_constraint, renaming, builder);
    }
    return builder.toString();
  }

  /** Returns the right replaceable policy. */
  public FreshRight queryRightReplaceablePolicy() {
    return queryProperties().rightReplaceablePolicy();
  }

  // ============================== correctness checking starts here ==============================

   /**
   * Helper function for the constructor: this checks that the rule is properly set up, e.g., no
   * null components, left- and right-hand side have the same type, and both sides are closed.
   */
  private void checkCorrectness() {
    checkNothingNull();
    checkTypesCorrect();
    checkBothSidesClosed();    // we'll check the constraint separately
    checkLeftNotTheory();
    checkConstraintTheory();
    checkConstraintFirstOrder();
  }

  /** Checks that no parts of a rule are null. */
  private void checkNothingNull() {
    if (_left == null) throw new NullStorageException("Rule", "left-hand side");
    if (_right == null) throw new NullStorageException("Rule", "right-hand side");
    if (_constraint == null) throw new NullStorageException("Rule", "constraints");
  }

  /** Checks that both sides of a rule have the same type, and the constraint has type Bool */
  private void checkTypesCorrect() {
    if (!_left.queryType().equals(_right.queryType())) {
      throw new TypingException("Rule", "checkTypesCorrect", "right-hand side",
                                _right.queryType().toString(), _left.queryType().toString());
    }
    Type t = _constraint.queryType();
    if (!t.equals(TypeFactory.boolSort) || !t.isTheoryType()) {
      throw new IllegalRuleException("constraint [" + _constraint.toString() + "] does not " +
        "have the theory sort Bool (it has type " + t.toString() + ").");
    }
  }

  /** Checks that both left- and right-hand side are closed. */
  private void checkBothSidesClosed() {
    if (!_left.isClosed()) { 
      throw new IllegalRuleException("left-hand side of rule [" + toString() + "] is not closed " +
        "(that is, freely contains a binder-variable).");
    }
    if (!_right.isClosed()) { 
      throw new IllegalRuleException("right-hand side of rule [" + toString() + "] is not closed " +
        "(that is, freely contains a binder-variable).");
    }
  }

  /**
   * Checks that the left-hand side cannot be instantiated to a theory term.
   * (Note that this is certainly the case if it is both a pattern and a theory term, but some
   * non-theory terms can still be instantiated to theory.)
   */
  private void checkLeftNotTheory() {
    LinkedList<Term> parts = new LinkedList<Term>();
    parts.add(_left);
    boolean couldBeTheory = true;
    while (!parts.isEmpty() && couldBeTheory) {
      Term t = parts.pop();
      if (!t.queryType().isTheoryType()) couldBeTheory = false;
      else if (t.isVariable() || t.isMetaApplication()) continue;
        // the arguments of a meta-variable may be ignored by the instantiation
      else if (t.isConstant()) couldBeTheory = t.queryRoot().isTheorySymbol();
      else if (t.isAbstraction()) parts.add(t.queryAbstractionSubterm());
      else if (t.isApplication()) {
        parts.add(t.queryHead());
        for (int i = 1; i <= t.numberArguments(); i++) parts.add(t.queryArgument(i));
      }
      else if (t.isTuple()) {
        for (int i = 1; i <= t.numberTupleArguments(); i++) parts.add(t.queryTupleArgument(i));
      }
    }
    if (couldBeTheory) {
      if (_left.isTheoryTerm()) {
        throw new IllegalRuleException("left-hand side of rule [" + toString() +
          "] is a theory term!");
      }
      else {
        throw new IllegalRuleException("left-hand side of rule [" + toString() +
          "] could be instantiated to a theory term!");
      }
    }
  }

  /** Checks that the constraint is a theory term. */
  private void checkConstraintTheory() {
    if (!_constraint.isTheoryTerm()) {
      throw new IllegalRuleException("constraint [" + _constraint.toString() +
        "] is not a theory term.");
    }
  }

  /** Checks that the constraint is a first-order term. */
  private void checkConstraintFirstOrder() {
    if (!_constraint.isFirstOrder()) {
      throw new IllegalRuleException("constraint [" + _constraint.toString() +
        "] is not first-order.");
    }
  }
}

