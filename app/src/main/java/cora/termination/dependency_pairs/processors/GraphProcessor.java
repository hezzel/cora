package cora.termination.dependency_pairs.processors;

import cora.data.digraph.Digraph;
import cora.data.digraph.SCC;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.List;

public class GraphProcessor implements Processor {

  @Override
  public boolean isApplicable(Problem dpp) { return true; }

  // This function implements an over approximation algorithm needed to turn a DP problem into a Digraph.
  private boolean isDpConnected(DP u, DP v) {
    return u.rhs().queryRoot().equals(v.lhs().queryRoot());
  }

  @Contract("_ -> new")
  @NotNull Digraph problemToGraph(@NotNull Problem dpp) {
    // Java is smart enough to realize a copy of dpp.getDPList() isn't really necessary,
    // so it will copy a reference of it to the local variable dps.
    List<DP> dps = dpp.getDPList();

    Digraph graphOfProblem = new Digraph(dpp.getDPList().size());
    // Notice that in this graph, each vertex represents i represent exactly
    // the DP at index i in the list dps.
    // This is not enforced by code (which would use memory/time).

    for(int i = 0; i < dps.size(); i++) {
      for (int j = 0; j < dps.size(); j++) {
        if (isDpConnected(dps.get(i), dps.get(j)))
          graphOfProblem.addEdge(i, j);
      }
    }

    System.out.println("List of DP Problems received: \n" + dpp.getDPList() );

     System.out.println("graph of problem: \n" + graphOfProblem);

    return graphOfProblem;
  }

  List<Problem> computeAllSubproblems(Problem dpp) {
    Digraph graphOfDPP = problemToGraph(dpp);
    SCC scc = new SCC(graphOfDPP);
    // We need to filter out the nontrivial SCCs from the SCC data in the scc object.
    List< List<Integer> > nonTrivalSCCs = scc.getSccData()
      .stream()
      .filter ( component ->
        component.size() > 1
          ||
          (component.size() == 1 && graphOfDPP.getNeighbors(component.getFirst()).contains(component.getFirst()))
      ).toList();
    System.out.println("SCC Processing...\nVertex on each nontrivial SCCs: " + nonTrivalSCCs);
    int numberOfNontrivialSCCs = nonTrivalSCCs.size();

    List< List<DP> > retDP            = new ArrayList<>(numberOfNontrivialSCCs);
    List< Digraph  > retGraph         = new ArrayList<>(numberOfNontrivialSCCs);
    List< Problem >  subproblems      = new ArrayList<>(numberOfNontrivialSCCs);

    // Here we process each nontrivial SCC component and generate a new DP Problem out of them.
    for(int i = 0; i < numberOfNontrivialSCCs; i++) {
      retDP.add(new ArrayList<>());

      List<Integer> sccVertices = nonTrivalSCCs.get(i);

      // For each vertex v in the SCC i, we collect the DPs that are in position v
      // from the dpp list of DPs (dpp.getDPList()).
      // Recall that in the associated graph of a DP problem,
      // each vertex v in the graph directly points to the element of this list at position v.
      // This observation is important, so the bijection between the nodes of the DP graph and
      // the DP problem's list of DPs is always maintained.
      // Warning: doing crazy shit with this association will only bring caos and despair.
      // We don't want that, do we? Coq will know if you did crazy shit... So beware of it.
      for(int vertex : sccVertices) {
        retDP.get(i).add(dpp.getDPList().get(vertex));
      }

      retGraph.add(graphOfDPP.getSubgraph(sccVertices));

      subproblems.add(new Problem(retDP.get(i), retGraph.get(i)));
    }

    return subproblems;
  }

  public List<Problem> processDPP(Problem dpp) {
    return computeAllSubproblems(dpp);
  }
}
