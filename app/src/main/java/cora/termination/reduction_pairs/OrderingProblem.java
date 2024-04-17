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

import com.google.common.collect.ImmutableList;
import java.util.List;

import charlie.terms.*;
import charlie.trs.Rule;
import charlie.trs.TRS;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.termination.reduction_pairs.OrderingRequirement.Relation;

/**
 * An OrderingProblem represents a list of requirements s ≻ t / s ≽ t that should be satisfied by
 * a reduction pair.
 *
 * Here, the problem is to find a reduction pair such that s ≻ t for the strict requirements,
 * s ≽ t for the weak requirements, and either s ≻ t or s ≽ for the remaining requirements, but we
 * are always required to orient at least one inequality strictly (so using ≻).
 *
 * The OrderingProblem keeps track of a TRS to impose the restrictions of term formation; its rules
 * are not directly used.
 */
public record OrderingProblem(ImmutableList<OrderingRequirement> reqs, TRS trs) {
  /** Add variables from FV(right) \ FV(left) into the given constraint. */
  private static Term fixConstraint(Term left, Term right, Term constraint) {
    Environment<Variable> lvars = left.vars();
    Environment<Variable> rvars = right.vars();
    Environment<Variable> cvars = constraint.vars();
    for (Variable x : rvars) {
      if (lvars.contains(x)) continue;
      if (cvars.contains(x)) continue;
      constraint = TermFactory.createApp(TheoryFactory.andSymbol, constraint,
        TermFactory.createApp(TheoryFactory.equalSymbol, x, x));
    }   
    return constraint;
  }

  /**
   * Helper function: updates the given immutable list builder with requirements l [rel] r | φ for
   * all rules l → r | φ in the given TRS.
   */
  private static void orient(TRS trs, Relation rel, ImmutableList.Builder<OrderingRequirement> b) {
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      Rule rule = trs.queryRule(i);
      Term left = rule.queryLeftSide();
      Term right = rule.queryRightSide();
      Term constr = fixConstraint(left, right, rule.queryConstraint());
      OrderingRequirement req = new OrderingRequirement(left, right, constr, rel);
      b.add(req);
    }
  }

  /** Creates an OrderingProblem where all rules in the TRS must be oriented strictly. */
  public static OrderingProblem createStrictProblem(TRS trs) {
    ImmutableList.Builder<OrderingRequirement> b = ImmutableList.<OrderingRequirement>builder();
    orient(trs, Relation.Strict, b);
    return new OrderingProblem(b.build(), trs);
  }

  /** Creates an OrderingProblem where at least one rule in the TRS must be oriented strictly. */
  public static OrderingProblem createNonStrictProblem(TRS trs) {
    ImmutableList.Builder<OrderingRequirement> b = ImmutableList.<OrderingRequirement>builder();
    orient(trs, Relation.Either, b);
    return new OrderingProblem(b.build(), trs);
  }

  /**
   * Creates an OrderingProblem where the rules in the TRS must be oriented weakly, and the
   * additional requirements must also be satisfied.
   * The given "extra" requirements will be stored at the start of the OrderingProblem, so their
   * index coincides with the index in a potential ReductionPairProofObject.
   */
  public static OrderingProblem createWeakProblem(TRS trs, List<OrderingRequirement> extra) {
    ImmutableList.Builder<OrderingRequirement> b = ImmutableList.<OrderingRequirement>builder();
    for (OrderingRequirement req : extra) b.add(req);
    orient(trs, Relation.Either, b);
    return new OrderingProblem(b.build(), trs);
  }

  /** Prints the current OrderingRequirement to the given OutputModule (as a table) */
  public void printTo(OutputModule module) {
    module.startTable();
    for (OrderingRequirement req : reqs) {
      req.printTo(module);
      module.println();
    }
    module.endTable();
  }

  /**
   * Returns a string representative of the problem.
   * This is only meant for debug output, as it is quite inefficient! (It creates a whole new
   * output module just for the printing).
   */
  public String toString() {
    OutputModule module = DefaultOutputModule.createUnicodeModule(trs);
    printTo(module);
    return module.toString();
  }
}

