package cora.termination.dependency_pairs.processors;

import java.util.List;
import java.util.ArrayList;
import java.util.TreeSet;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.termination.reduction_pairs.*;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.DP;

public class HorpoProcessor implements Processor {
  @Override
  public boolean isApplicable(Problem dp) {
    return Horpo.applicable(dp.getOriginalTRS());
  }

  private class HorpoProofObject extends ProcessorProofObject {
    private ReductionPairProofObject _result;

    /** Used for a failed proof */
    public HorpoProofObject(Problem dpp, ReductionPairProofObject result) {
      super(dpp);
      _result = result;
    }

    /** Used for a successful proof */
    public HorpoProofObject(Problem in, TreeSet<Integer> removed, ReductionPairProofObject result) {
      super(in, makeDPPList(in, removed));
      _result = result;
    }

    private static List<Problem> makeDPPList(Problem input, TreeSet<Integer> remove) {
      Problem out = input.removeDPs(remove, true);
      if (out.isEmpty()) return List.of();
      return List.of(out);
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
                                       OrderingRequirement.Relation.Either, dp.lvars()));
    }
    OrderingProblem problem = OrderingProblem.createWeakProblem(dpp.getOriginalTRS(), reqs);
    Horpo horpo = new Horpo(false);
    ReductionPairProofObject result = horpo.orient(problem);
    if (result.queryAnswer() == ProofObject.Answer.YES) {
      TreeSet<Integer> remove = new TreeSet<Integer>();
      for (int i = 0; i < dps.size(); i++) {
        if (result.isStrictlyOriented(i)) remove.add(i);
      }
      return new HorpoProofObject(dpp, remove, result);
    }
    else return new HorpoProofObject(dpp, result);
  }
}
