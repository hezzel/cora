package cora.termination.dependency_pairs;

import charlie.terms.Substitution;
import charlie.terms.Term;
import charlie.terms.TermFactory;
import charlie.terms.TheoryFactory;
import charlie.terms.Variable;
import charlie.util.Renamer;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.StreamSupport;

/**
 * Docu-guess (Carsten):
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
 * @param vars those variables of the DP that must be instantiated with
 *             theory terms; must contain all variables of constraint
 * @param isPrivate true if the DP is private; false otherwise
 */
public record DP(Term lhs, Term rhs, Term constraint, List<Variable> vars, boolean isPrivate) {

  private static boolean initialVarSetCondition(Term constraint, List<Variable> set) {
    List<Variable> constraintVars =
      StreamSupport
        .stream(constraint.vars().spliterator(), false)
        .toList();
    // ImplementationNotice (Deivid):
    // this hashSet wrapper of set around the list set is for performance...
    /// the thing is containsAll is too slow even for the close deadline here
    // hashSet makes it doable
     return new HashSet<>(set).containsAll(constraintVars);
  }

  public DP(Term lhs, Term rhs, Term constraint, List<Variable> vars, boolean isPrivate) {
    //TODO do null checking
    this.lhs = lhs;
    this.rhs = rhs;
    this.constraint = constraint;
    this.isPrivate = isPrivate;
    // the initial condition must be satisfied, otherwise we don't even create
    // the DP object, the lower bound however is higher than Vars(Phi)
    // and that's why we compute it here at object creation
    if (initialVarSetCondition(constraint, vars)) {
      this.vars = vars;
    } else {
      throw new IllegalArgumentException("Illegal DP construction: the list of variables " +
        vars + " for the DP must contain at least the variables in the constraint " +
        constraint.toString() + ".");
    }
  }

  /**
   * Creates a new DP of the following form s => t [true | emptySet ].
   * This constructor is mostly used for testing, as the constraint is forcedly
   * set as the TRUE value and the set V is empty.
   * It would also work for FO usages of the DP framework.
   * @param lhs
   * @param rhs
   */
  public DP(Term lhs, Term rhs) {
    this(lhs, rhs, TheoryFactory.createValue(true), List.of(), true);
  }

  /**
   *
   * @return a set of all variables occurring in this DP; may be modified
   */
  public Set<Variable> getAllVariables() {
    Set<Variable> result = new LinkedHashSet<>();
    for (Variable x : this.lhs.vars()) {
      result.add(x);
    }
    for (Variable x : this.rhs.vars()) {
      result.add(x);
    }
    for (Variable x : this.constraint.vars()) {
      result.add(x);
    }
    result.addAll(this.vars);
    return result;
  }
  @Override
  public String toString() {
    if (vars.size() == constraint.vars().size()) {
      return STR."\{lhs.toString()} -> \{rhs.toString()} [ \{constraint.toString()} ] ";
    }
    else {
      StringBuilder builder = new StringBuilder();
      builder.append(lhs.toString());
      builder.append(" -> ");
      builder.append(rhs.toString());
      builder.append(" [ ");
      builder.append(constraint.toString());
      builder.append(" | ");
      boolean first = true;
      for (Variable x : vars) {
        if (first) first = false;
        else builder.append(", ");
        builder.append(x.toString());
      }
      builder.append("]");
      return builder.toString();
    }
  }
}
