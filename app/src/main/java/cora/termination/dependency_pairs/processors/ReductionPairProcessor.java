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

package cora.termination.dependency_pairs.processors;

import java.util.List;
import java.util.ArrayList;
import java.util.TreeSet;
import charlie.trs.Rule;
import charlie.smt.SmtProblem;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.termination.reduction_pairs.*;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.DP;

public class ReductionPairProcessor implements Processor {
  private ReductionPair _redpair;

  private static Problem _cachedDPP = null;
  private static SmtProblem _cachedSMT = null;
  private static OrderingProblem _cachedOP = null;

  /**
   * Creates a processor based on the given reduction pair. This is allowed to be a weakly monotonic
   * pair (but if it is strongly monotonic, that's fine too).
   */
  public ReductionPairProcessor(ReductionPair rp) {
    _redpair = rp;
  }

  /**
   * Makes the ordering problem for the given DP Problem.
   * This uses caching: if we ask for the same DP problem multiple times, the corresponding ordering
   * problem is not recalculated.
   */
  private OrderingProblem makeOProb(Problem dpp) {
    if (dpp == _cachedDPP) return _cachedOP;
    _cachedSMT = new SmtProblem();
    OrderingProblem oprob =
      new OrderingProblem(dpp.getOriginalTRS(), new ArgumentFilter(_cachedSMT));
    List<DP> dps = dpp.getDPList();
    for (int i = 0; i < dps.size(); i++) {
      DP dp = dps.get(i);
      oprob.requireEither(new OrderingRequirement(dp.lhs(), dp.rhs(), dp.constraint(),
                                                  OrderingRequirement.Relation.Strict,
                                                  dp.lvars()), i);
    }
    for (Rule rule : dpp.getRuleList()) {
      oprob.require(new OrderingRequirement(rule, OrderingRequirement.Relation.Weak));
    }
    _cachedDPP = dpp;
    _cachedOP = oprob;
    return oprob;
  }

  /**
   * This returns true if the underlying reduction pair is (or may be) applicable to the ordering
   * problem for the given DP problem.
   */
  @Override
  public boolean isApplicable(Problem dpp) {
    return !dpp.hasExtraRules() &&
           _redpair.isApplicable(makeOProb(dpp));
  }

  @Override
  public ProcessorProofObject processDPP(Problem dpp) {
    OrderingProblem oprob = makeOProb(dpp);
    String name = _redpair.toString();
    if (!_redpair.isApplicable(oprob)) return new RPProofObject(name, dpp);
    ReductionPairProofObject result = _redpair.solve(oprob, _cachedSMT);
    _cachedOP = null;   // we used the SMT problem, so now we'll have to
    _cachedSMT = null;  // generate a new ordering problem the next time
    _cachedDPP = null;  // we try this
    if (result.queryAnswer() == ProofObject.Answer.YES) {
      TreeSet<Integer> remove = new TreeSet<Integer>();
      List<DP> dps = dpp.getDPList();
      for (int i = 0; i < dps.size(); i++) {
        if (result.isStrictlyOriented(i)) remove.add(i);
      }
      Problem altered = dpp.removeDPs(remove, true);
      return new RPProofObject(name, dpp, altered, result);
    }
    else return new RPProofObject(name, dpp, result);
  }
}

class RPProofObject extends ProcessorProofObject {
  private String _name;
  private ReductionPairProofObject _result;

  /** Used if the reduction pair is inapplicable */
  RPProofObject(String name, Problem dpp) {
    super(dpp);
    _name = name;
    _result = null;
  }

  /** Used for a failed proof */
  public RPProofObject(String name, Problem dpp, ReductionPairProofObject result) {
    super(dpp);
    _name = name;
    _result = result;
  }

  /** Used for a successful proof */
  public RPProofObject(String name, Problem in, Problem out, ReductionPairProofObject result) {
    super(in, out.isEmpty() ? List.of() : List.of(out));
    _name = name;
    _result = result;
  }

  public String queryProcessorName() { return "Reduction Pair [with " + _name + "]"; }

  public void justify(OutputModule module) {
    if (_result == null) module.println("Cannot apply " + _name + " to this problem.");
    else _result.justify(module);
    if (_output.size() == 0) module.println("All dependency pairs were removed.");
  }
}
