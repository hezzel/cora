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

package cora.termination.dependency_pairs.processors.graph;

import cora.config.Settings;
import cora.data.digraph.Digraph;
import cora.data.digraph.SCC;
import cora.io.OutputModule;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.processors.Processor;
import cora.termination.dependency_pairs.processors.ProcessorProofObject;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

public class GraphProcessor implements Processor {
  /** This technique can be disabled by runtime arguments. */
  public static String queryDisabledCode() { return "graph"; }

  @Override
  public boolean isApplicable(Problem dpp) {
    return !Settings.isDisabled(queryDisabledCode());
  }

  /** Returns a graph approximation for the given DP problem */
  private Digraph computeGraph(Problem dpp) {
    return Approximator.problemToGraph(dpp);
  }

  /** Computes the list of subproblems for the given DP problem and graph */
  private List<Problem> computeAllSubproblems(Problem dpp, Digraph graphOfDPP) {
    SCC scc = new SCC(graphOfDPP);
    // We need to filter out the nontrivial SCCs from the SCC data in the scc object.
    List< List<Integer> > nonTrivalSCCs = scc.getSccData()
      .stream()
      .filter ( component ->
        component.size() > 1 || (component.size() == 1 &&
          graphOfDPP.getNeighbours(component.getFirst()).contains(component.getFirst()))
      ).toList();

    int numberOfNontrivialSCCs = nonTrivalSCCs.size();

    // Here we process each nontrivial SCC component and generate a new DP Problem out of them.
    List<Problem> subproblems = new ArrayList<>(numberOfNontrivialSCCs);
    for (int i = 0; i < numberOfNontrivialSCCs; i++) {
      List<Integer> sccVertices = nonTrivalSCCs.get(i);
      List<DP> dps = new ArrayList<DP>();
      // For each vertex v in the SCC i, we collect the DPs that are in position v
      // from the dpp list of DPs (dpp.getDPList()).
      // Recall that in the associated graph of a DP problem,
      // each vertex v in the graph directly points to the element of this list at position v.
      // This observation is important, so the bijection between the nodes of the DP graph and
      // the DP problem's list of DPs is always maintained.
      // Warning: doing crazy shit with this association will only bring caos and despair.
      for (int vertex : sccVertices) dps.add(dpp.getDPList().get(vertex));
      subproblems.add(new Problem(dps, dpp.getRuleList(), Set.of(), dpp.getOriginalTRS(),
        dpp.isInnermost(), dpp.hasExtraRules(), dpp.queryTerminationStatus()));
      // NOTE: if we wanted to save the relevant subgraph into the DP problem (this is a reasonable
      // optimisation to consider in the future), we could do so using
      // graphOfDPP.getSubgraph(sccVertices)
    }

    return subproblems;
  }

  private class GraphProofObject extends ProcessorProofObject {
    private Digraph _graph;

    public GraphProofObject(Problem inp, Digraph graph) { super(inp); _graph = graph; }
    
    public GraphProofObject(Problem inp, List<Problem> out, Digraph graph) {
      super(inp, out);
      _graph = graph;
    }
    
    public String queryProcessorName() { return "Graph"; }
    
    public void justify(OutputModule module) {
      module.println("We compute a graph approximation with the following edges:");
      module.startTable();
      for (int i = 0; i < _input.getDPList().size(); i++) {
        Set<Integer> neighbours = _graph.getNeighbours(i);
        module.nextColumn("" + (i+1) + ":");
        for (int n : neighbours) module.print("" + (n + 1) + " ");
        module.println();
      }
      module.endTable();
      if (_output == null) module.println("All DPs are on the same SCC.");
      else if (_output.size() == 0) {
        module.println("As there are no SCCs, this DP problem is removed.");
      }
      else if (_output.size() == 1) {
        module.println("There is only one SCC, so all DPs not inside the SCC can be removed.");
      }
      else module.println("There are " + _output.size() + " SCCs.");
    }
  }

  @Override
  public ProcessorProofObject processDPP(Problem dpp) {
    Digraph graph = computeGraph(dpp);
    List<Problem> ret = computeAllSubproblems(dpp, graph);
    if (ret.size() == 1 && ret.get(0).getDPList().size() == dpp.getDPList().size()) {
      return new GraphProofObject(dpp, graph);
    }
    return new GraphProofObject(dpp, ret, graph);
  }
}

