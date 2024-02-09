package cora.termination.dependency_pairs.processors;

import cora.App;
import cora.data.digraph.Digraph;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;

import java.util.List;
import java.util.Optional;

public class ReachabilityProcessor implements Processor {

  @Override
  public boolean isApplicable(Problem dpp) {
    return true;
  }

  private void computeReachability(Problem dpp) {

    Digraph overApproximationGraph = Approximator.problemToGraph(dpp);

    List<DP> publicDPs = dpp
      .getDPList()
      .stream()
      .filter(dp -> !dp.isPrivate())
      .toList();

  }



  /**
   * @param dpp
   * @return
   */
  @Override
  public Optional<List<Problem>> processDPP(Problem dpp) {
    return Optional.empty();
  }

}
