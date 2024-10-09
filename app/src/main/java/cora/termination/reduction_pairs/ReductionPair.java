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

import charlie.smt.SmtProblem;

public interface ReductionPair {
  /**
   * This returns whether the current reduction pair is strongly monotonic (so s ≻ t implies
   * C[s] ≻ C[t]) or only weakly monotonic (so s ≽ t implies C[s] ≽ C[t]).
   */
  public boolean isStronglyMonotonic();

  /**
   * Checks that the given ordering problem satisfies the requirements to try and apply this
   * particular reduction pair (for example by a check on the term restrictions in the
   * underlying TRS).
   */
  public boolean isApplicable(OrderingProblem prob);

  /**
   * Given an OrderingProblem, and an SMT-problem that may already have some restrictions on the
   * monotonicity requirements and constraints in that ordering problem, this function aims to find
   * a satisfying assignment to the SMT-problem that also orients the ordering problem (as needed by
   * the valuation).
   */
  public ReductionPairProofObject solve(OrderingProblem prob, SmtProblem smt);

  /** Returns a unique name for the reduction pair, to be used in printing proofs. */
  public String queryName();
}
