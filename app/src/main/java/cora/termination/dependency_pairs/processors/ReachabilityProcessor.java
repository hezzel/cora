package cora.termination.dependency_pairs.processors;

import cora.io.OutputModule;
import cora.config.Settings;
import cora.data.digraph.Digraph;
import cora.data.digraph.Reachability;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;

import java.util.ArrayList;
import java.util.List;

public class ReachabilityProcessor implements Processor {
  /** This technique can be disabled by runtime arguments. */
  public static String queryDisabledCode() { return "reach"; }

  @Override
  public boolean isApplicable(Problem dp) { return !Settings.isDisabled(queryDisabledCode()); }

  private class ReachabilityProofObject extends ProcessorProofObject {
    public ReachabilityProofObject(Problem inp) { super(inp); }
    public ReachabilityProofObject(Problem inp, Problem out) { super(inp, out); }
    public void justify(OutputModule module) {
      int num = _input.getDPList().size() - _output.get(0).getDPList().size();
      if (num == 0) module.println("All dependency pairs are reachable.");
      else if (num == 1) {
        module.println("There is one unreachable dependency pair, which is removed.");
      }
      else module.println("There are %a unreachable dependency pairs, which are removed.", num);
    }
    public String queryProcessorName() { return "Reachability"; }
  }

  public ProcessorProofObject transform(Problem dpp) {

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
      // TODO: give the processor more information about _which_ DPs got removed
      return new ReachabilityProofObject(dpp, ret);
    } else {
      return new ReachabilityProofObject(dpp);
    }
  }

  @Override
  public ReachabilityProofObject processDPP(Problem dpp) {
    // Since this is a pre-processor I am returning a failure
    return new ReachabilityProofObject(dpp);
  }

}
