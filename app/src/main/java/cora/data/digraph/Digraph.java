package cora.data.digraph;

import cora.exceptions.IllegalArgumentError;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

//TODO: complete this documentation with more information about the implementation of digraphs.
/**
 * <p>This class implements a data structure for Digraphs.
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

  /**
   *  The number of vertices in the digraph.
   */
  private int _numberOfVertices;

  /**
   * The number of edges in the digraph.
   */
  private int _numberOfEdges;

  /**
   * The adjacency list of the digraph.
   */
  private final List< List<Integer> > _adjacencyList;

  /**
   * <p>Initializes a digraph with {@code numberOfVertices} vertices.</p>
   * <p>No edge is added to the graph.</p>
   * @param numberOfVertices the total number of vertices in the graph
   * @throws IllegalArgumentError if {@code numberOfVertices < 0}
   */
  public Digraph(int numberOfVertices) {
    if (numberOfVertices < 0) {
      throw new IllegalArgumentError(
        "Digraph",
        "Digraph",
        "trying to instantiate a digraph with negative number of vertices"
      );
    }

    _numberOfVertices = numberOfVertices;
    _numberOfEdges = 0;
    _adjacencyList = new ArrayList< List<Integer> >(_numberOfEdges);

    for(int i = 0; i < _numberOfVertices; i++){
      _adjacencyList.add( new ArrayList<Integer>());
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
   * This method check for the bounds of a given vertex.
   */
  private void checkVerticesBounds(int vertex, String method) {
    if (vertex < 0 || vertex > this.getNumberOfVertices() - 1) {
      throw new IllegalArgumentError(
        "Digraph",
        method,
        STR."vertex with value \{vertex} out of bound, it should be in the range 0 - \{this.getNumberOfVertices() - 1}"
      );
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
   * Adds an edge connecting {@code originVertex} to {@code destinationVertex}.
   *
   * @param originVertex the origin vertex
   * @param destinationVertex the destination vertex
   * @throws IllegalArgumentError if {@code originVertex < 0} or {@code originVertex >
   *   getNumberOfVertices()} and, analogously, if
   *   {@code destinationVertex < 0} or {@code destinationVertex > getNumberOfVertices()}
   */
  public void addEdge(int originVertex, int destinationVertex) {
    // Some sanitization checking before adding the edge.
    if(this.getNumberOfVertices() == 0) {
      throw new IllegalArgumentError(
        "Digraph",
        "addEdge",
        "this digraph has no vertex, so it is not possible to add an edge to an empty digraph.\n"+
          "Users can manually add vertices with the method Digraph::addVertex"
      );
    }
    if(originVertex < 0 || originVertex >= _numberOfVertices) {
      throw new IllegalArgumentError(
        "Digraph",
        "addEdge",
        STR."the vertex argument originVertex is out of bounds, it should be in the range 0 - \{getNumberOfEdges() - 1}"
      );
    }
    if(destinationVertex < 0 || destinationVertex >= _numberOfVertices) {
      throw new IllegalArgumentError(
        "Digraph",
        "addEdge",
        STR."the vertex argument destinationVertex is out of bounds, it should be in the range 0 - \{getNumberOfEdges() - 1}"
      );
    }
    //If all checking above pass, then we finally add the edge in the adjacency list.
    _adjacencyList.get(originVertex).add(destinationVertex);
    _numberOfEdges++;
  }

  /**
   * Returns whether two vertices {@code origin} and {@code destination} are adjacent,
   * that is, if there is an edge from {@code origin} to {@code destination}.
   * @param origin the origin vertex
   * @param destination the destination vertex
   * @throws IllegalArgumentError if either {@code origin} or {@code destination} are out of bound
   */
  public boolean isAdjacent(int origin, int destination) {
    checkVerticesBounds(origin,"isAdjacent");
    checkVerticesBounds(destination, "isAdjacent");

    Stream<Integer> test = _adjacencyList
      .get(origin)
      .stream()
      .filter(i -> i == destination);
    return test.findAny().isPresent();
  }

  /**
   * <p>Returns the list of all vertices {@code y} such that there exists
   * an edge from {@code originVertex} to {@code y}.
   * </p>
   * @param originVertex the origin vertex
   */
  public List<Integer> getNeighbors(int originVertex) {
    checkVerticesBounds(originVertex, "Digraph");
    return _adjacencyList.get(originVertex);
  }

  public String toString() {
    StringBuilder ret = new StringBuilder();
    for (int i = 0; i < _numberOfVertices; i++) {
      ret.append(i).append(" |-> ").append(_adjacencyList.get(i)).append("\n");
    }
    return ret.toString();
  }

}
