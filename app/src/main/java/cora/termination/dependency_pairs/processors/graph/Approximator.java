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

import cora.data.digraph.Digraph;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;

import java.util.List;

/** This is a helper class used to create a dependency graph approximation. */
public class Approximator {
  public static Digraph problemToGraph(Problem dpp) {
    List<DP> dps = dpp.getDPList();
    Digraph graphOfProblem = new Digraph(dps.size());
    // Notice that in this graph, each vertex represents i represent exactly
    // the DP at index i in the list dps.
    // This is not enforced by code (which would use memory/time).

    ApproximateReducer reducer = new ApproximateReducer(dpp.getOriginalTRS(), dpp.getRuleList());
    boolean bad = !reducer.isApplicable();

    for (int i = 0; i < dps.size(); i++) {
      for (int j = 0; j < dps.size(); j++) {
        // if the reducer doesn't apply, we just check preservation of the root symbol
        if (bad) {
          if (dps.get(i).rhs().queryRoot().equals(dps.get(j).lhs().queryRoot())) {
            graphOfProblem.addEdge(i, j);
          }
        }
        // if it does apply, that's what we check instead!
        else {
          if (reducer.mayReduce(dps.get(i), dps.get(j))) graphOfProblem.addEdge(i, j);
        }
      }
    }
    return graphOfProblem;
  }
}

