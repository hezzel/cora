package cora.termination.dependency_pairs.processors;

import cora.App;
import cora.data.digraph.Digraph;
import cora.data.digraph.Reachability;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.certification.Informal;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

public class ReachabilityProcessor implements Processor {

  @Override
  public boolean isApplicable(Problem dpp) {
    return true;
  }

  public Problem transform(Problem dpp) {

    Digraph overApproximationGraph = Approximator.problemToGraph(dpp);

    // We first collect the indexes of those dps that are public in the
    // dpp problem.

    List<Integer> publicDPsIndex = dpp
      .getDPList()
      .stream()
      .filter(dp -> !dp.isPrivate())
      .map(dp -> dpp.getDPList().indexOf(dp))
      .toList();

    // Then we use the Reachability data structure, it saves the indexes of all vertices in the
    // given graph
    Reachability reachability = new Reachability(overApproximationGraph, publicDPsIndex);

    if (dpp.getDPList().size() > reachability.getReachableVertices().size()) {
      List<DP> newDps = reachability
        .getReachableVertices()
        .stream()
        .map( index -> dpp.getDPList().get(index))
        .toList();
      Problem ret = new Problem(newDps, dpp.getTRS());
      Informal.getInstance().addProofStep(
        "***** Investigating the following DP problem using the reachability processor:");
      Informal.getInstance().addProofStep(dpp.toString());
      Informal.getInstance().addProofStep("We remove " +
        (dpp.getDPList().size() - reachability.getReachableVertices().size()) +
        " unreachable dependency pairs.\n");
      return ret;
    } else {
      return dpp;
    }
  }

  /**
   * @param dpp
   * @return
   */
  @Override
  public Optional<List<Problem>> processDPP(Problem dpp) {
    // Since this is a pre-processor I am returning nothing...
    // TODO build proper interfacing for processors and pre-processors
    return Optional.empty();
  }

}
