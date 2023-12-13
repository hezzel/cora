package cora.data.digraph;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

class SCCTest {

  @Test
  void testBasicSCC(){
    Digraph g = new Digraph(3);

    g.addEdge(0,1);
    g.addEdge(1,0);
//    g.addEdge(2,0);

    SCC scc = new SCC(g);

    System.out.println(g);

    System.out.println("This graph has " + scc.getNumberOfSCCs() + " components.");

    // we then compute the list of vertices on each strongly component
    List< List<Integer>> components = new ArrayList<>(scc.getNumberOfSCCs());
    for(int i = 0; i < scc.getNumberOfSCCs(); i++){
      components.add(new ArrayList<>());
    }
    for(int v = 0; v < g.getNumberOfVertices(); v++){
      components.get(scc.getSccId(v)).add(v);
    }

    //print the whole thingy
    for(int i = 0; i < scc.getNumberOfSCCs(); i++){
      for(int v : components.get(i)){
        System.out.print(v + " ");
      }
      System.out.println();
    }

    TransitiveClosure tc = new TransitiveClosure(g);

  }



}
