package cora.data.digraph;

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

    int temp = 0;
    while(temp != source){
      temp = stack.pop();
      _sccId[temp] = _numberOfSCCs;
      _low[temp] = graph.getNumberOfVertices();
    }
    _numberOfSCCs++;
  }

  public int getNumberOfSCCs(){ return _numberOfSCCs; }

  public boolean isStronglyConnected(int source, int destination){
    return _sccId[source] == _sccId[destination];
  }

  public int getSccId(int v) { return _sccId[v]; }

}
