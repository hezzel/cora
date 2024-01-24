package cora.termination.dependency_pairs;

import cora.terms.Term;
import cora.terms.TheoryFactory;

public record DP(Term lhs, Term rhs, Term constraint) {

  public DP(Term lhs, Term rhs, Term constraint) {
    // do null checkings
    this.lhs = lhs;
    this.rhs = rhs;
    this.constraint = constraint;
  }

  public DP(Term lhs, Term rhs) {
    this(lhs, rhs, TheoryFactory.createValue(true));
  }

  @Override
  public String toString() {
    return lhs.toString() + " -> " + rhs.toString() + " [ " + constraint.toString() + " ] ";
  }
}
