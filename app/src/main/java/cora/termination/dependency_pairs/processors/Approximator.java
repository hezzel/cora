package cora.termination.dependency_pairs.processors;

import cora.data.digraph.Digraph;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;

import java.util.List;

public class Approximator {

  // This function implements an over approximation algorithm needed to turn a
  // DP problem into a Digraph.
  private static boolean isDpConnected(Problem dpp, DP u, DP v) {
    OverApproximation overApproximation = new OverApproximation(dpp.getTRS());
    return overApproximation.mayReduce(u, v);
  }

  @Contract("_ -> new")
  @NotNull
  public static Digraph problemToGraph(@NotNull Problem dpp) {
    // Java is smart enough to realize a copy of dpp.getDPList() isn't really necessary,
    // so it will copy a reference of it to the local variable dps.
    List<DP> dps = dpp.getDPList();

    Digraph graphOfProblem = new Digraph(dpp.getDPList().size());
    // Notice that in this graph, each vertex represents i represent exactly
    // the DP at index i in the list dps.
    // This is not enforced by code (which would use memory/time).

    for(int i = 0; i < dps.size(); i++) {
      for (int j = 0; j < dps.size(); j++) {
        if (isDpConnected(dpp, dps.get(i), dps.get(j)))
          graphOfProblem.addEdge(i, j);
      }
    }
    return graphOfProblem;
  }
}
