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

package cora.termination.dependency_pairs;

import charlie.terms.*;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Dependency Pair for Logically Constrained Simply-typed Term Rewrite Systems
 * (LCSTRSs) as introduced in:
 *<p>
 * Liye Guo, Kasper Hagens, Cynthia Kop, Deivid Vale:
 * Higher-Order Constrained Dependency Pairs for (Universal) Computability.
 * MFCS 2024: 57:1-57:15
 *
 * @param lhs the left-hand side of the DP
 * @param rhs the right-hand side of the DP
 * @param constraint the constraint of the DP
 * @param lvars those variables of the DP that must be instantiated with
 *             theory terms; must contain all variables of constraint
 */
public record DP(Term lhs, Term rhs, Term constraint, Set<Variable> lvars) {
  /** This verifies that all variables in the constraint are in the list */
  private static boolean initialVarSetCondition(Term constraint, Set<Variable> set) {
    return set.containsAll(constraint.vars().toSet());
  }

  /**
   * Default constructor: creates a DP with the given left-hand side, right-hand side, constraint
   * and logical variables; the set of logical variables must contain all the variables occurring
   * in constraint, or an IllegalArgumentException will be thrown.
   */
  public DP(Term lhs, Term rhs, Term constraint, Set<Variable> lvars) {
    this.lhs = lhs;
    this.rhs = rhs;
    this.constraint = constraint;
    // the initial condition must be satisfied, otherwise we don't even create
    // the DP object, the lower bound however is higher than Vars(Phi)
    // and that's why we compute it here at object creation
    if (initialVarSetCondition(constraint, lvars)) this.lvars = lvars;
    else {
      throw new IllegalArgumentException("Illegal DP construction: the list of variables " +
        lvars + " for the DP must contain at least the variables in the constraint " +
        constraint.toString() + ".");
    }
  }

  /**
   * Creates a DP with the given left-hand side, right-hand side and constraint.  The logical
   * variables will automatically be set to the variables occurring in the constraint.
   */
  public DP(Term lhs, Term rhs, Term constraint) {
    this(lhs, rhs, constraint, constraint.vars().toSet());
  }

  /** Creates a new DP of the form s ⇒ t | true {}, to be used for unconstrained rewriting. */
  public DP(Term lhs, Term rhs) {
    this(lhs, rhs, TheoryFactory.createValue(true), Set.of());
  }

  /**
   * @return a modifiable set of all variables occurring in this DP
   */
  public LinkedHashSet<Variable> getAllVariables() {
    LinkedHashSet<Variable> result = new LinkedHashSet<>();
    for (Variable x : this.lhs.vars()) result.add(x);
    for (Variable x : this.rhs.vars()) result.add(x);
    for (Variable x : this.constraint.vars()) result.add(x);
    return result;
  }

  /**
   * @return a DP that is structurally equivalent to the present one but uses fresh variables
   */
  public DP getRenamed() {
    Substitution subst = TermFactory.createEmptySubstitution();
    for (Variable x : getAllVariables()) {
      subst.extend(x, TermFactory.createVar(x.queryName(), x.queryType()));
    }
    Term newLhs = this.lhs.substitute(subst);
    Term newRhs = this.rhs.substitute(subst);
    Term newConstraint = this.constraint.substitute(subst);
    Set<Variable> newTheoryVars = new LinkedHashSet<>();
    for (Variable x : this.lvars) {
      Term y = subst.get(x);
      if (y != null) newTheoryVars.add(y.queryVariable());
    }
    return new DP(newLhs, newRhs, newConstraint, newTheoryVars);
  }

  /**
   * Default toString() functionality; deliberately ugly because printing to the user should always
   * be done through an output module.
   */
  @Override
  public String toString() {
    return toString(new Renaming(Set.of()));
  }

  /** Better toString() functionality for a given Renaming */
  public String toString(Renaming renaming) {
    StringBuilder builder = new StringBuilder();
    TermPrinter printer = new TermPrinter(Set.of());
    printer.print(lhs, renaming, builder);
    builder.append(" => ");
    printer.print(rhs, renaming, builder);
    builder.append(" | ");
    printer.print(constraint, renaming, builder);
    builder.append(" {");
    boolean first = true;
    for (Variable x : lvars) {
      if (constraint.vars().contains(x)) continue;
      if (first) { first = false; builder.append(" "); }
      else builder.append(", ");
      printer.print(x, renaming, builder);
    }
    builder.append(" }");
    return builder.toString();
  }
}

