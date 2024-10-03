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

import charlie.util.Pair;
import charlie.terms.FunctionSymbol;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.termination.reduction_pairs.OrderingRequirement.Relation;

import java.util.ArrayList;
import java.util.Set;
import java.util.function.BiFunction;

/**
 * A Proof Object variant specifically for the result of reduction pairs, which can be queried for
 * the OrderingRequirements that were strictly oriented.
 */
public abstract class ReductionPairProofObject implements ProofObject {
  protected Set<Integer> _strictlyOriented;
    // this stores the identifiers of the Either requirements that were strictly oriented, and is
    // set to null for a failed proof!
  protected ArrayList<OrderingRequirement> _reqs;
    // this stores the actual requirements that we have oriented, or is null for a failed proof
  protected BiFunction<FunctionSymbol,Integer,Boolean> _regards;
    // this stores the regards function that was actually used, or is null for a failed proof

  /**
   * Initialise a successful proof, for the given problem, with the given identifiers within the
   * problem being oriented strictly (and the rest of the either requirements weakly).  The second
   * set lists the indexes of those conditional requirements for which the condition was satisfied
   * (and thus which have also been oriented).
   */
  protected ReductionPairProofObject(OrderingProblem problem, Set<Integer> strictlyOriented,
                                     Set<Integer> conditionSatisfied,
                                     BiFunction<FunctionSymbol,Integer,Boolean> regards) {
    _strictlyOriented = strictlyOriented;
    _reqs = new ArrayList<OrderingRequirement>();
    _regards = regards;

    // store either requirements, after figuring out whether they're strictly or weakly oriented
    for (Pair<Integer,OrderingRequirement> p : problem.eitherReqs()) {
      Relation rel = strictlyOriented.contains(p.fst()) ? Relation.Strict : Relation.Weak;
      _reqs.add(new OrderingRequirement(p.snd().left(), p.snd().right(), p.snd().constraint(),
                rel, p.snd().tvar()));
    }
    // store unconditional requirements
    _reqs.addAll(problem.unconditionalReqs());
    // store conditional requirements for which the condition is satisfied
    int n = problem.conditionalReqs().size();
    for (int i = 0; i < n; i++) {
      if (conditionSatisfied.contains(i)) _reqs.add(problem.conditionalReqs().get(i).snd());
    }
  }

  /** Initialise a failed proof for the given problem. */
  protected ReductionPairProofObject(OrderingProblem problem) {
    _strictlyOriented = null;
    _reqs = null;
    _regards = null;
  }

  /**
   * Returns YES if this was a successful proof of the given OrderingProblem (even if not all
   * OrderingRequirements have been strictly oriented yet), and MAYBE otherwise.
   */
  public Answer queryAnswer() {
    if (_reqs == null) return Answer.MAYBE;
    else return Answer.YES;
  }

  /**
   * This returns whether the "either" OrderingRequirement with the given identifier in the ordering
   * problem was strictly oriented.
   *
   * In the case of a failed proof, this always returns false.
   */
  public final boolean isStrictlyOriented(int identifier) {
    if (_strictlyOriented == null) return false;
    return _strictlyOriented.contains(identifier);
  }

  /**
   * This returns whether the chosen reduction pair regards the given position of the given function
   * symbol.
   */
  public final boolean regards(FunctionSymbol f, int index) {
    if (_regards == null) return false;
    return _regards.apply(f, index);
  }

  /**
   * This prints a table describing the ordering problem to the given output module, without
   * "Either" or conditional option:
   *
   * - for the "Either" requirements, the strictly oriented requirements are printed with a strict
   *   ordering, and the others with a weak ordering;
   * - for the conditional requirements, only the ones for which the constraint is satisfied are
   *   printed (without their constraint)
   */
  protected void printOrderingProblem(OutputModule module) {
    module.startTable();
    for (OrderingRequirement req : _reqs) {
      req.printTo(module);
      module.println();
    }
    module.endTable();
  }

  /**
   * This function is used to either explain the failure (if queryAnswer() == MAYBE), or justify
   * the success and which requirements were strictly oriented (if queryAnswer() == YES).
   */
  public abstract void justify(OutputModule module);
}
