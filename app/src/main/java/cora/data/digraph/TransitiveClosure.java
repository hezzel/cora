package cora.data.digraph;

public class TransitiveClosure {

  private Reachability[] _allReachability;


  TransitiveClosure(Digraph g) {
    _allReachability = new Reachability[g.getNumberOfVertices()];
    for(int i = 0; i < g.getNumberOfVertices(); i++){
      _allReachability[i] = new Reachability(g, i);
    }
  }

  boolean isReachable(int origin, int destination) {
    return _allReachability[origin].isReachable(destination);
  }

}
