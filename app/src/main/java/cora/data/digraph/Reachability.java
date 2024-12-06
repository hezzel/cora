package cora.data.digraph;

import java.util.ArrayList;
import java.util.List;

/**
 *  This class holds the data for the reachability problem on digraphs.
 *  It provides two constructors:
 *  <ul>
 *    <li>{@code Reachability(Digraph graph, int source)}</li>
 *    <li>{@code Reachability(Digraph graph, Iterable<Integer> sources)}</li>
 *  </ul>
 *  <p>
 *  In the first case, given a {@code Digraph graph} and a vertex {@code int source}.
 *  This object holds all vertices {@code v} from {@code graph} such that there exists a path from
 *  {@code source} to {@code v}.
 *  </p>
 *
 *  <p>
 *  In the second case, given a {@code Digraph graph} and a collection of vertices
 *  {@code Iterable<Integer> sources}.
 *  This object holds all vertices {@code v} such that there exists a path from any vertex in
 *  {@code sources} to {@code v}.
 *  </p>
 *
 *  <p>
 *    Notice that instantiating an object of this class computes the solution to the reachability
 *    problem and save the result as data in the object.
 *  </p>
 */
public class Reachability {

  /**
   * This vector is a bookkeeper for the reachability status of all vertices in the input grpah
   * that is reachable from either the vertex source or the list of vertex source.
   */
  private final boolean[] _isReachable;


  /**
   * TODO: add docs
   * @param graph
   * @param source
   */
  public Reachability(Digraph graph, int source){
    _isReachable = new boolean[graph.getNumberOfVertices()];
    reachabilitySearch(graph, source);
  }

  /**
   * TODO: add docs
   * @param graph
   * @param sources
   */
  public Reachability(Digraph graph, Iterable<Integer> sources) {
    _isReachable = new boolean[graph.getNumberOfVertices()];
    for(int s : sources)
      if (!_isReachable[s]) reachabilitySearch(graph, s);
  }

  /**
   * Implements a depth-first search for the reachable vertices starting from source.
   */
  private void reachabilitySearch(Digraph graph, int source) {
    _isReachable[source] = true;
    for(int v : graph.getNeighbours(source))
      if (!_isReachable[v]) reachabilitySearch(graph,v);
  }

  /**
   * Returns whether the parameter {@code destination} is reachable from the <i>source</i>.
   * @param destination
   */
  public boolean isReachable(int destination) { return _isReachable[destination]; }

  /**
   * Returns the list of all vertices that are reachable from <i>source</i>.
   * @return
   */
  public List<Integer> getReachableVertices() {
    List<Integer> ret = new ArrayList<>();
    for(int i = 0; i < _isReachable.length; i++){
      if (_isReachable[i]) ret.add(i);
    }
    return ret;
  }

  @Override
  public String toString() {
    return getReachableVertices().toString();
  }
}
