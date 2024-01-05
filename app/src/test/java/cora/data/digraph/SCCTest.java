package cora.data.digraph;

import cora.data.digraph.Digraph;
import cora.data.digraph.SCC;
import cora.data.digraph.TransitiveClosure;
import org.junit.jupiter.api.Test;

class SCCTest {

  @Test
  void testBasicSCC(){
    Digraph g = new Digraph(3);

    g.addEdge(0,1);
    g.addEdge(1,0);
//    g.addEdge(2,0);

    SCC scc = new SCC(g);

//    System.out.println(g);

//    System.out.println(scc);

  }
}
