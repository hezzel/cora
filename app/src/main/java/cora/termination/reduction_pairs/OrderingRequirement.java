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

package cora.termination.reduction_pairs;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.Collections;

import charlie.util.Pair;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.Renaming;
import charlie.trs.Rule;
import cora.io.OutputModule;

/**
 * An OrderingRequirement is a constrained requirement left R right [constraint], where R is either
 * ≻ or ≽.  It is particularly used in an OrderingProblem.
 *
 * The set tvar is unmodifiable.
 */
public record OrderingRequirement(Term left, Term right, Term constraint, Relation rel,
                                  Set<Variable> tvar) {
  public enum Relation { Strict, Weak }

  /**
   * Creates an OrderingRequirement based on the given terms and set.
   * Note that the set should not be modified afterwards: it is stored inside the record.
   */
  public OrderingRequirement(Term l, Term r, Term co, Relation relation, Collection<Variable> tv) {
    this(l, r, co, relation, Collections.unmodifiableSet(new TreeSet<Variable>(tv)));
  }

  /**
   * Creates an OrderingRequirement based on the left-hand side, right-hand side, constraint and
   * lvars of the given rule, with the given relation.
   */
  public OrderingRequirement(Rule rho, Relation relation) {
    this(rho.queryLeftSide(), rho.queryRightSide(), rho.queryConstraint(), relation,
         Collections.unmodifiableSet(new TreeSet<Variable>(rho.queryLVars())));
  }

  /**
   * Prints the current requirement to the given module (within the current paragraph or column;
   * no structural commands are used, so this can safely be added in the middle of a sentence).
   */
  public void printTo(OutputModule module) {
    Renaming naming = module.queryTermPrinter().generateUniqueNaming(left, right, constraint);
    String relation = switch (rel) {
      case Strict -> "%{succ}";
      case Weak -> "%{succeq}";
    };
    Pair<Term,Renaming> l = new Pair<Term,Renaming>(left, naming);
    Pair<Term,Renaming> r = new Pair<Term,Renaming>(right, naming);
    Pair<Term,Renaming> c = new Pair<Term,Renaming>(constraint, naming);
    module.print("%a " + relation + " %a", l, r);
    if (!constraint.isValue() || !constraint.toValue().getBool()) module.print(" | %a", c);
    // print the extra variables only if necessary
    boolean allvarsinconstraint = true;
    for (Variable x : tvar) {
      if (!constraint.vars().contains(x)) {
        if (left.vars().contains(x) || right.vars().contains(x)) {
          allvarsinconstraint = false;
          break;
        }
      }
    }
    if (!allvarsinconstraint) {
      module.print(" { ");
      for (Variable x : tvar) {
        // only show the variables that actually occur
        if (!left.vars().contains(x) && !right.vars().contains(x) &&
            !constraint.vars().contains(x)) continue;
        module.print("%a ", new Pair<Term,Renaming>(x, naming));
      }
      module.print("}");
    }
  }
  
  /** Should only be used for debug output (and is deliberately ugly to make that clear) */
  public String toString() {
    return left.toString() + " " + rel + " " + right.toString() + " | " + constraint.toString() +
      " {" + tvar.toString() + " }";
  }
}

