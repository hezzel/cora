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

package cora.data.digraph;

import charlie.exceptions.IndexingError;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.TreeMap;

/**
 * <p>This class implements a data structure for directed graphs, without parallel edges.
 * Since names of vertices are not important in a generic implementation of graphs, we name them
 * here by integers, ranging from {@code 0} to a non-negative integer parameter
 * {@code numberOfVertices - 1} given at construction. </p>
 *
 * <p><b>Note.</b> Whenever a new graph is created its set of edges is empty.
 * Users then are allowed to add edges via the method {@code addEdges(int sourceVertex, int
 * destinationVertex)}.
 * </p>
 */
public class Digraph {
  private int _numberOfVertices;
  private int _numberOfEdges;
  private final List< Set<Integer> > _adjacencyList;

  /**
   * <p>Initializes a digraph with {@code numberOfVertices} vertices.</p>
   * <p>No edge is added to the graph.</p>
   * @param numberOfVertices the total number of vertices in the graph
   * @throws IllegalArgumentException if {@code numberOfVertices < 0}
   */
  public Digraph(int numberOfVertices) {
    if (numberOfVertices < 0) {
      throw new IllegalArgumentException("instantiating a digraph with negative vertices count");
    }

    _numberOfVertices = numberOfVertices;
    _numberOfEdges = 0;
    _adjacencyList = new ArrayList< Set<Integer> >(_numberOfEdges);

    for (int i = 0; i < _numberOfVertices; i++) {
      _adjacencyList.add(new TreeSet<Integer>());
    }
  }

  /** Returns the number of vertices in the digraph. */
  public int getNumberOfVertices() { return _numberOfVertices; }

  /** Returns the number of edges in the digraph. */
  public int getNumberOfEdges() { return _numberOfEdges; }

  /**
   * This method check for the bounds of a given integer and test whether it is in range for
   * vertices in the graph.
   *
   * @param vertex the integer parameter to be checked as vertex
   * @param method the method in the class name
   *
   * @throws IndexingError if the {@code vertex} parameter is out of bounds for this graph; that is,
   * {@code vertex < 0 || vertex > this.getNumberOfVertices() - 1}.
   */
  private void validateVertex(int vertex, String method) {
    if (vertex < 0 || vertex >= _numberOfVertices) {
      throw new IndexingError("Digraph", method, vertex, 0, _numberOfVertices-1);
    }
  }

  /** Adds a vertex to the digraph. Its index is set as {@code getNumberOfVertices()}. */
  public void addVertex() {
    _numberOfVertices++;
    _adjacencyList.add(new TreeSet<>());
  }

  /**
   * Adds a directed edge connecting {@code originVertex} to {@code destinationVertex}.
   * If such an edge is already present nothing is done since we do not allow for parallel edges.
   * @param originVertex the origin vertex
   * @param destinationVertex the destination vertex
   * @throws IndexingError if {@code originVertex < 0} or {@code originVertex >=
   *   getNumberOfVertices()} and, analogously, if
   *   {@code destinationVertex < 0} or {@code destinationVertex >= getNumberOfVertices()}
   */
  public void addEdge(int originVertex, int destinationVertex) {
    // Some sanitization checking before adding the edge.
    validateVertex(originVertex, "addEdge");
    validateVertex(destinationVertex, "addEdge");
    // We only add the edge originVertex -> destinationVertex if it is not there already.
    Set<Integer> targets = _adjacencyList.get(originVertex);
    if (!targets.contains(destinationVertex)) {
      targets.add(destinationVertex);
      _numberOfEdges++;
    }
  }

  /**
   * Removes (if present) the edge with origin in {@code originVertex} and destination in
   * {@code destinationVertex}.  If not present, nothing is done.
   * @param originVertex the origing vertex
   * @param destinationVertex the destination vertex
   * @throws IndexingError if either the first or second parameter is out of bounds related
   * to the number of vertices in the graph
   */
  public void removeEdge(int originVertex, int destinationVertex) {
    validateVertex(originVertex, "removeEdge");
    validateVertex(destinationVertex, "removeEdge");
    Set<Integer> targets = _adjacencyList.get(originVertex);
    if (targets.contains(destinationVertex)) {
      targets.remove(destinationVertex);
      _numberOfEdges--;
    }
  }

  /**
   * Returns whether two vertices {@code origin} and {@code destination} are adjacent;
   * that is, if there is an edge from {@code origin} to {@code destination}.
   * @param originVertex the origin vertex
   * @param destinationVertex the destination vertex
   * @throws IndexingError if either {@code origin} or {@code destination} are out of bounds
   */
  public boolean isAdjacent(int originVertex, int destinationVertex) {
    validateVertex(originVertex,"isAdjacent");
    validateVertex(destinationVertex, "isAdjacent");
    return _adjacencyList.get(originVertex).contains(destinationVertex);
  }

  /**
   * <p>Returns the set of all vertices {@code y} such that there exists
   * an edge from {@code originVertex} to {@code y}.
   * </p>
   *
   * <p>The caller cannot modify tihs set.  To add a neighbour, instead use addEdge.</p>
   * @param originVertex the origin vertex
   */
  public Set<Integer> getNeighbours(int originVertex) {
    validateVertex(originVertex, "getNeighbours");
    return Collections.unmodifiableSet(_adjacencyList.get(originVertex));
  }


  /**
   * Given a list of vertices in this graph, this method returns the subgraph that has this list
   * as the set of vertices. Edges are preserved as in the original graph, except for those that
   * point to a vertex that is not in the list.
   * @param vertices a list of vertices
   * @return the subgraph that has {@code vertices} as the set of vertex
   * @throws IndexingError if any of the integers in the {@code vertices} list is out of bounds
   */
  public Digraph getSubgraph(List<Integer> vertices) {
    // Note: the comments below are a bit long, but they are included because it is easy to get
    // confused with the indexes.
    // Recall that the argument list contains the indexes names from the original graph, say G.
    // We want to construct the subgraph H of G using the indexes in [vertices], but note that in
    // H, those vertices will be renamed 0..vertices.size()-1.
    Digraph subGraph = new Digraph(vertices.size());
    TreeMap<Integer,Integer> newindex = new TreeMap<Integer,Integer>();

    // Determine the new name for each of the given vertices, and store it in newindex.
    for (int i = 0; i < vertices.size(); i++) {
      int v = vertices.get(i);
      validateVertex(v, "getSubgraph");
      newindex.put(v, i);
    }

    // Now, we have to correctly add the edges back, even though the names changed in the subgraph.
    // What we need to guarantee is that the {@code subGraph} is isomorphic to H.
    for (int v : vertices) {
      int id = newindex.get(v);
      // Then we get all neighbours, in G, of this vertex v.
      Set<Integer> neighbours = _adjacencyList.get(v);
      // For each of the neigbhours that occurs in H, also add the edge in H
      for (int n : neighbours) {
        if (newindex.containsKey(n)) subGraph.addEdge(id, newindex.get(n));
      }
    }
    return subGraph;
  }

  /** Returns a string representation of the graph for debugging purposes. */
  public String toString() {
    StringBuilder ret = new StringBuilder();
    for (int i = 0; i < _numberOfVertices; i++) {
      ret.append(i).append(" |-> ").append(_adjacencyList.get(i)).append("\n");
    }
    return ret.toString();
  }
}
