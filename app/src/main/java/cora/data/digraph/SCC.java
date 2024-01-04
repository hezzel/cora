package cora.data.digraph;

import cora.exceptions.IllegalArgumentError;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

public class SCC {

  private final boolean[] _visided;
  private final int[] _sccId;
  private final int[] _low;
  private final Stack<Integer> stack;
  private int _pre;
  private int _numberOfSCCs;

  public SCC(Digraph graph) {
    _visided = new boolean[graph.getNumberOfVertices()];
    stack = new Stack<>();
    _sccId = new int[graph.getNumberOfVertices()];
    _low = new int[graph.getNumberOfVertices()];
    for(int i = 0; i < graph.getNumberOfVertices(); i++){
      if (!_visided[i]) sccSearch(graph,i);
    }
  }

  private void sccSearch(Digraph graph, int source) {
    _visided[source] = true;
    _low[source] = _pre++;
    int minValue = _low[source];
    stack.push(source);

    for(int neighbor : graph.getNeighbors(source)){
      if(!_visided[neighbor]) {
        sccSearch(graph, neighbor);
      }
      if(_low[neighbor] < minValue) {
        minValue = _low[neighbor];
      }
    }

    if(minValue < _low[source]) {
      _low[source] = minValue;
      return;
    }

    int temp;
    do {
      temp = stack.pop();
      _sccId[temp] = _numberOfSCCs;
      _low[temp] = graph.getNumberOfVertices();
    } while (temp != source);
    _numberOfSCCs++;
  }

  private void validateVertex(int vertex, String method) {
    //we can validate the bounds using _visited since it has exactly the same number of elements
    // as in the graph's number of vertices, which is defined at construction.
    int bound = _visided.length;
    if (vertex < 0 || vertex > bound - 1) {
      throw new IllegalArgumentError(
        "SCC",
        method,
        STR."vertex with value \{vertex} out of bound, it should be in the range 0 - \{bound - 1}"
      );
    }
  }

  /**
   * Returns the number of strongly connected components the graph has.
   */
  public int getNumberOfSCCs(){ return _numberOfSCCs; }

  /**
   * Check whether {@code source} is strongly connected with {@code destination}.
   * Recall that two nodes in a directed graph are strongly connected if there exist a directed path
   * from {@code soure} to {@code destination} and a directed path from {@code destination} to
   * {@code source}. From the SCC algorithm computed by the constructor of this object, we just
   * return whether {@code source} and {@code destination} belong to the same strongly connected
   * component.
   */
  public boolean isStronglyConnected(int source, int destination){
    validateVertex(source, "isStronglyConnected");
    validateVertex(destination, "isStronglyConnected");

    return _sccId[source] == _sccId[destination];
  }

  /**
   * Returns the identifier (or index) of the strongly connected component to which the parameter
   * vertex belongs to.
   */
  public int getSccId(int vertex) {
    validateVertex(vertex, "getSccId");
    return _sccId[vertex];
  }

  /**
   * Returns the data stored in this SCC object.
   * The return data is of type {@code List< List<Integer> >} in which the outermost list stores
   * the data of each scc component in the graph. So the lenght of this list is equal to
   * {@code this.getNumberOfSccs}. Each component is identified by their index in this list.
   * @return
   */
  public List<List<Integer>> getSccData() {
    List< List<Integer> > components = new ArrayList<>(this.getNumberOfSCCs());
    for(int i = 0; i < this.getNumberOfSCCs(); i++){
      components.add(new ArrayList<>());
    }
    for(int v = 0; v < _visided.length; v++){
      components.get(this.getSccId(v)).add(v);
    }
    return components;
  }

  @Override
  public String toString() {
    StringBuilder ret = new StringBuilder();
    List< List<Integer> > components = this.getSccData();
    for(int i = 0; i < this.getNumberOfSCCs(); i++){
      ret.append("Component ").append(i).append(": ").append(components.get(i)).append("\n");
    }
    return ret.toString();
  }
}
