package cora.termination.dependency_pairs.processors;

import com.google.common.collect.ImmutableList;
import cora.data.digraph.Digraph;
import cora.data.digraph.SCC;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import cora.utils.Pair;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class GraphProcessor implements Processor {

  @Override
  public boolean isApplicable(DP dpp) { return true; }


  // TODO Implement the real function here. This function is dummy.
  private boolean isDpConnected(DP u, DP v) {
    Random random = new Random();
    return random.nextBoolean();
  }

  @Contract("_ -> new")
  private @NotNull Digraph problemToGraph(@NotNull Problem dpp) {
    // Implementation notice: this guarantees that dps
    // is a locally immutable reference to dpp's elements.
    // copyOf is smart enough to realize an actual deep copy isn't necessary
    // (when that is really the case)
    List<DP> dps = dpp.getProblem();

    // Now in this digraph each node represents one DP problem in sequence.
    Digraph graphOfProblem = new Digraph(dpp.getProblem().size());

    for(int i = 0; i < dps.size(); i++) {
      for (int j = 0; j < dps.size(); j++) {
        if (isDpConnected(dps.get(i), dps.get(j)))
          graphOfProblem.addEdge(i, j);
      }
    }

    return graphOfProblem;
  }

  private List<Problem> computeNewAllSubproblems(Problem dpp) {
    Digraph graphOfDPP = problemToGraph(dpp);
    SCC scc = new SCC(graphOfDPP);
    List< List<Integer> > sccData = scc.getSccData();

    //
    List< List<DP> > retDP    = new ArrayList<>(scc.getNumberOfSCCs());
    List< Digraph  > retGraph = new ArrayList<>(scc.getNumberOfSCCs());
    List< Problem >  ret      = new ArrayList<>(scc.getNumberOfSCCs());

    // Process each SCC to the new components of each problem to return
    for(int i = 0; i < scc.getNumberOfSCCs(); i++) {
      retDP.add(new ArrayList<>());

      List<Integer> sccVertices = sccData.get(i);
      for(int vertex : sccVertices) {
        retDP.get(i).add(dpp.getProblem().get(vertex));
      }
      retGraph.add(graphOfDPP.getSubgraph(sccVertices));

      ret.add(new Problem(retDP.get(i), retGraph.get(i)));
    }

    return ret;
  }

  public List<Problem> processDPP(Problem dpp) {
    return null;
  }



}
