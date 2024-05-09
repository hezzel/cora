package cora.termination.dependency_pairs.processors;

import java.util.List;
import java.util.ArrayList;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.termination.reduction_pairs.*;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.DP;

public class HorpoProcessor implements Processor {
  @Override
  public boolean isApplicable(Problem dp) {
    return Horpo.applicable(dp.getTRS());
  }

  private class HorpoProofObject extends ProcessorProofObject {
    private ReductionPairProofObject _result;

    /** Used for a failed proof */
    public HorpoProofObject(Problem dpp, ReductionPairProofObject result) {
      super(dpp);
      _result = result;
    }

    /** Used for a successful proof */
    public HorpoProofObject(Problem in, List<DP> remaining, ReductionPairProofObject result) {
      super(in, makeDPList(in, remaining));
      _result = result;
    }

    private static List<Problem> makeDPList(Problem input, List<DP> lst) {
      if (lst.size() == 0) return List.of();
      return List.of(new Problem(lst, input.getTRS()));
    }

    public String queryProcessorName() { return "horpo"; }

    public void justify(OutputModule module) {
      _result.justify(module);
      if (_output.size() == 0) module.println("All dependency pairs were removed.");
      else module.println("This leaves the following smaller problem:");
    }
  }

  @Override
  public ProcessorProofObject processDPP(Problem dpp) {
    ArrayList<OrderingRequirement> reqs = new ArrayList<OrderingRequirement>();
    List<DP> dps = dpp.getDPList();
    for (DP dp : dps) {
      reqs.add(new OrderingRequirement(dp.lhs(), dp.rhs(), dp.constraint(), 
                                       OrderingRequirement.Relation.Either, dp.vars()));
    }
    OrderingProblem problem = OrderingProblem.createWeakProblem(dpp.getTRS(), reqs);
    Horpo horpo = new Horpo(false);
    ReductionPairProofObject result = horpo.orient(problem);
    if (result.queryAnswer() == ProofObject.Answer.YES) {
      ArrayList<DP> lst = new ArrayList<DP>();
      for (int i = 0; i < dps.size(); i++) {
        if (!result.isStrictlyOriented(i)) lst.add(dps.get(i));
      }
      return new HorpoProofObject(dpp, lst, result);
    }
    else return new HorpoProofObject(dpp, result);
  }
}
