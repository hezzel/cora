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

import charlie.terms.Term;
import charlie.terms.TheoryFactory;
import charlie.terms.Variable;
import java.util.Set;
import java.util.stream.StreamSupport;

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

  /**
   * Creates a new DP of the form s ⇒ t | true {}, to be used for unconstrained rewriting.
   */
  public DP(Term lhs, Term rhs) {
    this(lhs, rhs, TheoryFactory.createValue(true), Set.of());
  }

  @Override
  public String toString() {
    StringBuilder builder = new StringBuilder();
    builder.append(lhs.toString());
    builder.append(" => ");
    builder.append(rhs.toString());
    builder.append(" | ");
    builder.append(constraint.toString());
    builder.append(" {");
    boolean first = true;
    for (Variable x : lvars) {
      if (constraint.vars().contains(x)) continue;
      if (first) { first = false; builder.append(" "); }
      else builder.append(", ");
      builder.append(x.toString());
    }
    builder.append(" }");
    return builder.toString();
  }
}
