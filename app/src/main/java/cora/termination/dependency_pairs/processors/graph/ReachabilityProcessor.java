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

import cora.io.OutputModule;
import cora.config.Settings;
import cora.data.digraph.Digraph;
import cora.data.digraph.Reachability;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.processors.Processor;
import cora.termination.dependency_pairs.processors.ProcessorProofObject;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

public class ReachabilityProcessor implements Processor {
  /** This technique can be disabled by runtime arguments. */
  public static String queryDisabledCode() { return "reach"; }

  @Override
  public boolean isApplicable(Problem dp) {
    return !Settings.isDisabled(queryDisabledCode()) &&
           dp.hasPrivateDPs();
  }

  @Override
  public ReachabilityProofObject processDPP(Problem dpp) {
    Digraph overApproximationGraph = Approximator.problemToGraph(dpp);

    // We first collect the indexes of those dps that are public in the
    // dpp problem.
    int n = dpp.getDPList().size();
    ArrayList<Integer> publicDPsIndex = new ArrayList<Integer>(n);
    for (int i = 0; i < n; i++) {
      if (!dpp.isPrivate(i)) publicDPsIndex.add(i);
    }

    // Then we use the Reachability data structure; it saves the indexes of all vertices in the
    // given graph
    Reachability reachability = new Reachability(overApproximationGraph, publicDPsIndex);

    int m = reachability.getReachableVertices().size();
    if (n > m) {
      ArrayList<DP> newDPs = new ArrayList<DP>(m);
      HashSet<Integer> newPrivate = new HashSet<Integer>(m);
      for (int index : reachability.getReachableVertices()) {
        if (dpp.isPrivate(index)) newPrivate.add(newDPs.size());
        newDPs.add(dpp.getDPList().get(index));
      }
      Problem ret = new Problem(newDPs, dpp.getRuleList(), newPrivate, dpp.getOriginalTRS(),
                                dpp.isInnermost(), dpp.hasExtraRules(),
                                dpp.queryTerminationStatus());
      return new ReachabilityProofObject(dpp, ret, overApproximationGraph);
    } else {
      return new ReachabilityProofObject(dpp, overApproximationGraph);
    }
  }
}

/** The processor proof object that the ReachabilityProcessor return. */
class ReachabilityProofObject extends ProcessorProofObject {
  private Digraph _graph;

  /** Used for a failed proof: nothing is removed. */
  public ReachabilityProofObject(Problem inp, Digraph graph) {
    super(inp);
    _graph = graph;
  }

  /** Used for a successful proof: at least one DP is removed. */
  public ReachabilityProofObject(Problem inp, Problem out, Digraph graph) {
    super(inp, out);
    _graph = graph;
  }

  /** Processor name, for printing by the proof object of the framework. */
  public String queryProcessorName() {
    return "Reachability";
  }

  /** Prints an explanation to the output. */
  public void justify(OutputModule module) {
    module.println("We compute a graph approximation with the following edges:");
    module.startTable();
    for (int i = 0; i < _input.getDPList().size(); i++) {
      if (_input.isPrivate(i)) module.nextColumn("");
      else module.nextColumn("!");
      Set<Integer> neighbours = _graph.getNeighbours(i);
      module.nextColumn("" + (i+1) + ":");
      for (int n : neighbours) module.print("" + (n + 1) + " ");
      module.println();
    }
    module.endTable();
    int num = _input.getDPList().size();
    if (_output.size() > 0) num = _input.getDPList().size() - _output.get(0).getDPList().size();
    if (num == 0) module.println("All dependency pairs are reachable.");
    else if (num == 1) {
      module.println("There is one unreachable dependency pair, which is removed.");
    }
    else if (num == _input.getDPList().size()) {
      module.println("There are no public dependency pairs, so clearly this problem is finite.");
    }
    else module.println("There are %a unreachable dependency pairs, which are removed.", num);
  }
}

