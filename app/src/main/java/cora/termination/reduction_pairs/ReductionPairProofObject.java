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

import java.util.Set;
import charlie.exceptions.IllegalArgumentError;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.termination.TerminationAnswer;
import cora.termination.reduction_pairs.OrderingRequirement.Relation;

/**
 * A Proof Object variant specifically for the result of reduction pairs, which can be queried for
 * the OrderingRequirements that were strictly oriented.
 */
public abstract class ReductionPairProofObject implements ProofObject {
  protected OrderingProblem _problem;
  protected Set<Integer> _strictlyOriented; // set to null for a failed proof!

  /**
   * Initialise a successful proof, for the given problem, with the given indexes within the problem
   * being oriented strictly (and the rest weakly).
   */
  protected ReductionPairProofObject(OrderingProblem problem, Set<Integer> strictlyOriented) {
    _problem = problem;
    _strictlyOriented = strictlyOriented;
  }

  /** Initialise a failed proof for the given problem. */
  protected ReductionPairProofObject(OrderingProblem problem) {
    _problem = problem;
    _strictlyOriented = null;
  }

  /**
   * Returns YES if this was a successful proof of the given OrderingProblem (even if not all
   * OrderingRequirements have been strictly oriented yet), and MAYBE otherwise.
   */
  public TerminationAnswer queryAnswer() {
    if (_strictlyOriented == null) return TerminationAnswer.MAYBE;
    else return TerminationAnswer.YES;
  }

  /**
   * This returns whether the OrderingRequirement with the given index in the ordering problem
   * was strictly oriented.
   *
   * In the case of a failed proof, this always returns false.
   */
  public final boolean isStrictlyOriented(int index) {
    if (_strictlyOriented == null) return false;
    return _strictlyOriented.contains(index);
  }

  /**
   * This returns whether the given OrderingRequirement was strictly oriented.  Note that this is
   * checked by pointer equality; recreating the same requirement to call this function will likely
   * cause an Error to be thrown, as will any call with a requirement that is not in the
   * OrderingProblem.
   *
   * In the case of a failed proof, this always returns false.
   */
  public final boolean isStrictlyOriented(OrderingRequirement req) {
    if (_strictlyOriented == null) return false;
    for (int i = 0; i < _problem.reqs().size(); i++) {
      if (_problem.reqs().get(i) == req) return _strictlyOriented.contains(i);
    }
    throw new IllegalArgumentError("ReductionPairProofObject", "isStrictlyOriented",
      "Given ordering requirement " + req.toString() + " was not in the original OrderingProblem.");
  }

  /**
   * This prints a table describing the ordering problem to the given output module, without
   * "Either" option: the strictly oriented requirements are ordered strictly, the weakly oriented
   * ones weakly.
   */
  protected void printOrderingProblem(OutputModule module) {
    module.startTable();
    for (int i = 0; i < _problem.reqs().size(); i++) {
      OrderingRequirement req = _problem.reqs().get(i);
      OrderingRequirement r = switch (req.rel()) {
        case Relation.Strict -> req;
        case Relation.Weak -> req;
        case Relation.Either ->
          new OrderingRequirement(req.left(), req.right(), req.constraint(),
                                  _strictlyOriented.contains(i) ? Relation.Strict : Relation.Weak);
      };
      r.printTo(module);
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
