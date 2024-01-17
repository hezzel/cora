package cora.termination.dependency_pairs;

import cora.terms.Term;

public record DP(Term lhs, Term rhs, Term constraint) {

  @Override
  public String toString() {
    return lhs.toString() + " -> " + rhs.toString() + " [ " + constraint.toString() + " ] ";
  }
}
