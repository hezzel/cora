package cora.data.digraph;

import charlie.exceptions.IndexingError;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * <p>This class implements a data structure for directed graphs.
 * The vertices names are not important in a generic implementation of graphs,
 * and here we name them by indexes ranging from {@code 0} to a non-negative integer parameter
 * {@code numberOfVertices} given at construction. </p>
 *
 * <p><b>Note.</b> Whenever a new graph is created its set of edges is empty.
 * Users then are allowed to add edges via the method {@code addEdges(int sourceVertex, int
 * destinationVertex)}.
 * </p>
 */
public class Digraph {
  private int _numberOfVertices;
  private int _numberOfEdges;
  private final List< List<Integer> > _adjacencyList;

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
    _adjacencyList = new ArrayList< List<Integer> >(_numberOfEdges);

    for (int i = 0; i < _numberOfVertices; i++){
      _adjacencyList.add(new ArrayList<Integer>());
    }
  }

  /**
   * Returns the number of vertices in the digraph.
   */
  public int getNumberOfVertices() { return _numberOfVertices; }

  /**
   * Returns the number of edges in the digraph.
   */
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

  /**
   * Adds a vertex to the digraph. Its index is set as {@code getNumberOfVertices()}.
   */
  public void addVertex() {
    _numberOfVertices++;
    _adjacencyList.add(new ArrayList<>());
  }

  /**
   * Adds a directed edge connecting {@code originVertex} to {@code destinationVertex}.
   * Notice that if such an edge is already present nothing is done.
   * @param originVertex the origin vertex
   * @param destinationVertex the destination vertex
   * @throws IndexingError if {@code originVertex < 0} or {@code originVertex >
   *   getNumberOfVertices()} and, analogously, if
   *   {@code destinationVertex < 0} or {@code destinationVertex > getNumberOfVertices()}
   */
  public void addEdge(int originVertex, int destinationVertex) {
    // Some sanitization checking before adding the edge.
    validateVertex(originVertex, "addEdge");
    validateVertex(destinationVertex, "addEdge");
    // We only add the edge originVertex -> destinationVertex if it is not there already.
    // The reason is that we don't allow for parallel edges in our applications.
    int lookUpIndex = _adjacencyList
      .get(originVertex)
      .indexOf(destinationVertex);

    if (lookUpIndex < 0) {
      _adjacencyList.get(originVertex).add(destinationVertex);
      _numberOfEdges++;
    }
  }

  /**
   * Removes (if present) the edge with origin in {@code originVertex} and destination in
   * {@code destinationVertex}.
   * @param originVertex the origing vertex
   * @param destinationVertex the destination vertex
   * @throws IndexingError if either the first or second parameter is out of bound related
   * to the number of vertices in the graph
   */
  public void removeEdge(int originVertex, int destinationVertex) {
    validateVertex(originVertex, "removeEdge");
    validateVertex(destinationVertex, "removeEdge");

    int lookUpIndex = _adjacencyList.get(originVertex).indexOf(destinationVertex);

    if (lookUpIndex >= 0) {
      _adjacencyList.get(originVertex).remove(lookUpIndex);
      _numberOfEdges--;
    }
  }

  /**
   * Returns whether two vertices {@code origin} and {@code destination} are adjacent,
   * that is, if there is an edge from {@code origin} to {@code destination}.
   * @param originVertex the origin vertex
   * @param destinationVertex the destination vertex
   * @throws IndexingError if either {@code origin} or {@code destination} are out of bounds
   */
  public boolean isAdjacent(int originVertex, int destinationVertex) {
    validateVertex(originVertex,"isAdjacent");
    validateVertex(destinationVertex, "isAdjacent");

    return _adjacencyList.get(originVertex).indexOf(destinationVertex) >= 0;
  }

  /**
   * <p>Returns the list of all vertices {@code y} such that there exists
   * an edge from {@code originVertex} to {@code y}.
   * </p>
   * @param originVertex the origin vertex
   */
  public List<Integer> getNeighbors(int originVertex) {
    validateVertex(originVertex, "getNeighbors");
    return _adjacencyList.get(originVertex);
  }


  /**
   * Given a list of vertices in this graph, this method returns the subgraph that has this list
   * as the set of vertices. Edges are preserved as in the original graph. Except those that
   * point to a vertex that is not in the list.
   * @param vertices a list of vertices
   * @return the subgraph that has {@code vertices} as the set of vertex
   * @throws IndexingError if any of the integers in the {@code vertices} list is out of bounds
   */
  public Digraph getSubgraph(@NotNull List<Integer> vertices) {
    // Note: the comments below are a bit unnecessary, but I guess someone reading this code years
    // from now may get confused with the indexes. So I wrote this in case you need.
    // If not, feel free to ignore it.
    // Recall that the argument list contains the indexes names from the original graph,
    // let us call it G, and we want to construct the subgraph H of G using those indexes.
    // When the new graph is created, of vertex-size vertices.size(),
    // we have that in the subgraph new indexes are created from 0 to vertices.size() - 1.

    Digraph subGraph = new Digraph(vertices.size());

    // Now, we have to correctly add the edges back, even though the names changed in the subgraph.
    // That is, the subgraph we will create renames its vertices by position.
    // This isn't a problem.
    // What we need to guarantee is that the {@code subGraph} is isomorphic to H.

    // Hence, in the code below, the variables v and n refer to an index in the graph G.
    // While in the subgraph, named "subGraph" in the code, each v is mapped to its index
    // in the argument list "vertices".
    for (int v : vertices) {
      // First we validate that each v in vertices is a valid index of G.
      this.validateVertex(v, "getSubgraph");
      // Then we get all neighbors, in G, of this vertex v.
      List<Integer> neighbors = this.getNeighbors(v);
      // Remove from the set of neighbors those indexes that doesn't occur in 'vertices'.
      neighbors.removeIf(x -> !vertices.contains(x));
      for(int n : neighbors) {
        // Now we add back those edges that are in G and should also be in the subgraph.
        // Here's where we get the indexOf v and n, since that's their new names in the subgraph.
        subGraph.addEdge(vertices.indexOf(v), vertices.indexOf(n));
      }
    }
    return subGraph;
  }

  public String toString() {
    StringBuilder ret = new StringBuilder();
    for (int i = 0; i < _numberOfVertices; i++) {
      ret.append(i).append(" |-> ").append(_adjacencyList.get(i)).append("\n");
    }
    return ret.toString();
  }

}
