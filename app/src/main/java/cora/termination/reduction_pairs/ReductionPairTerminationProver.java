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

import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.smt.SmtProblem;
import cora.io.OutputModule;
import cora.io.ProofObject;

/**
 * A termination prover that seeks to prove termination by orienting all rules in one go with a
 * strongly monotonic reduction pair.
 */
public class ReductionPairTerminationProver {
  private ReductionPair _reductionPair;

  /** Creates a prover for the given reduction pair, which must be strongly monotonic. */
  public ReductionPairTerminationProver(ReductionPair redpair) {
    _reductionPair = redpair;
    if (!redpair.isStronglyMonotonic()) {
      throw new IllegalArgumentException("The ReductionPairTerminationProver may only be called " +
        "with a strongly monotonic reduction pair; I was given " + redpair.toString());
    }
  }

  public ProofObject proveTermination(TRS trs) {
    SmtProblem smt = new SmtProblem();
    OrderingProblem prob = new OrderingProblem(trs, ArgumentFilter.createEmptyFilter(smt));
    for (Rule rule : trs.queryRules()) {
      prob.require(new OrderingRequirement(rule, OrderingRequirement.Relation.Strict));
    }
    if (!_reductionPair.isApplicable(prob)) {
      return new ReductionPairNotApplicableProofObject(_reductionPair.toString());
    }
    else return _reductionPair.solve(prob, smt);
  }
}

class ReductionPairNotApplicableProofObject implements ProofObject {
  private String _name;
  ReductionPairNotApplicableProofObject(String name) { _name = name; }
  public Answer queryAnswer() { return Answer.MAYBE; }
  public void justify(OutputModule module) {
    module.println("The current implementation of %a is not applicable to this TRS.", _name);
  }
}
