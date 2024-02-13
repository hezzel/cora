package cora.termination.dependency_pairs.processors;

import cora.data.digraph.Digraph;
import cora.data.digraph.SCC;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.certification.Informal;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

public class GraphProcessor implements Processor {

  @Override
  public boolean isApplicable(Problem dpp) { return true; }

  private List<Problem> computeAllSubproblems(@NotNull Problem dpp) {
    Digraph graphOfDPP = Approximator.problemToGraph(dpp);

    SCC scc = new SCC(graphOfDPP);
    // We need to filter out the nontrivial SCCs from the SCC data in the scc object.
    List< List<Integer> > nonTrivalSCCs = scc.getSccData()
      .stream()
      .filter ( component ->
        component.size() > 1
          ||
          (component.size() == 1 && graphOfDPP.getNeighbors(component.getFirst()).contains(component.getFirst()))
      ).toList();

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

      subproblems.add(new Problem(retDP.get(i), dpp.getTRS(), retGraph.get(i)));
    }

    return subproblems;
  }

  public Optional<List<Problem>> processDPP(Problem dpp) {
    List<Problem> ret = computeAllSubproblems(dpp);
    if (ret.size() == 1 && ret.get(0).getDPList().size() == dpp.getDPList().size()) {
      return Optional.empty();
    }

    Informal.getInstance().addProofStep(
      "***** Investigating the following DP problem using the graph processor:");
    Informal.getInstance().addProofStep(dpp.toString());
    if (ret.size() == 0) {
      Informal.getInstance().addProofStep(
        "As there are no SCCs, this DP problem is removed.");
    }
    else if (ret.size() == 1) {
      Informal.getInstance().addProofStep(
        "Using the graph processor, this DP problem is decreased to the following SCC:");
      Informal.getInstance().addProofStep(ret.get(0).toString());
    }
    else {
      Informal.getInstance().addProofStep(
        "Using the graph processor, this DP problem is split into the following SCCs:");
      for (int i = 0; i < ret.size(); i++) {
        if (i > 0) Informal.getInstance().addProofStep("And:");
        Informal.getInstance().addProofStep(ret.get(i).toString());
      }
    }

    return Optional.of(ret);
  }
}