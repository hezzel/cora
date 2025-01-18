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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.Collections;

import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.trs.Rule;
import charlie.printer.Printer;
import charlie.printer.PrintableObject;

/**
 * An OrderingRequirement is a constrained requirement left R right [constraint], where R is either
 * ≻ or ≽.  It is particularly used in an OrderingProblem.
 *
 * The set tvar is unmodifiable.
 */
public record OrderingRequirement(Term left, Term right, Term constraint, Relation rel,
                                  Set<Variable> tvar) implements PrintableObject {
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

  /** Prints the current requirement to the given printer. */
  public void print(Printer printer) {
    ArrayList<Object> components = new ArrayList<Object>();
    components.add(left);
    components.add(" ");
    components.add(switch(rel) {
      case Strict -> printer.symbSucc();
      case Weak -> printer.symbSucceq();
    });
    components.add(" ");
    components.add(right);
    if (!constraint.isValue() || !constraint.toValue().getBool()) {
      components.add(" | ");
      components.add(constraint);
    }
    if (!allVarsInConstraint()) {
      components.add(" { ");
      for (Variable x : tvar) {
        // only show the variables that actually occur
        if (!left.vars().contains(x) && !right.vars().contains(x) &&
            !constraint.vars().contains(x)) continue;
        components.add(x);
        components.add(" ");
      }
      components.add("}");
    }
    printer.add(components);
  }

  /**
   * Helper function for print: this returns whether or not all variables in tvar also occur in the
   * constraint.
   */
  private boolean allVarsInConstraint() {
    for (Variable x : tvar) {
      if (!constraint.vars().contains(x)) {
        if (left.vars().contains(x) || right.vars().contains(x)) return false;
      }
    }
    return true;
  }
  
  /** Should only be used for debug output (and is deliberately ugly to make that clear) */
  public String toString() {
    return left.toString() + " " + rel + " " + right.toString() + " | " + constraint.toString() +
      " {" + tvar.toString() + " }";
  }
}

