package cora.data.digraph;

import charlie.exceptions.IllegalArgumentError;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.Comparator;
import java.util.List;

class DigraphTest {

  @Test
  public void testBasicGraphs() {
    Digraph g = new Digraph(3);
    g.addEdge(0, 1);
    g.addEdge(0,1);
    g.addEdge(0, 2);
    g.addEdge(1, 0);
    g.addEdge(1, 2);
    g.addEdge(2, 1);
//    System.out.println(g);

    Digraph sub = g.getSubgraph(List.of(1,0));
//    System.out.println(sub);
  }

  @Test
  void testDigraphNegativeSizeCreation() {
    Assertions.assertThrows(IllegalArgumentError.class, () -> {
      Digraph g = new Digraph(-1);
    });
  }

  @Test
  void testAddEdgeToEmptyDigraph() {
    Assertions.assertThrows(IllegalArgumentError.class, () -> {
      Digraph g = new Digraph(0);
      g.addEdge(0,0);
    });
  }

  @Test
  void testAddDuplicatedEdge() {
    Digraph g = new Digraph(3);
    g.addEdge(0, 1);
    g.addEdge(0,1);
    Assertions.assertEquals(g.getNumberOfEdges(), 1);
  }

  @Test
  void tesAddingOutOfBoundsOrigin() {
    Assertions.assertThrows(IllegalArgumentError.class, () -> {
      Digraph g = new Digraph(3);
      g.addEdge(3,0);
    });
  }

  @Test
  void testAddingOutOfBoundsDestination() {
    Assertions.assertThrows(IllegalArgumentError.class, () -> {
      Digraph g = new Digraph(3);
      g.addEdge(0, 3);
    });
  }

  @Test
  void testRemovalOfEdges() {
    Digraph g = new Digraph(3);
    g.addEdge(0,1);
    Assertions.assertEquals(1, g.getNumberOfEdges());
    g.removeEdge(0,1);
    Assertions.assertEquals(0, g.getNumberOfEdges());

  }

  @Test
  void testIsAdjacent() {
    Digraph g = new Digraph(3);
    g.addEdge(0,1);
    Assertions.assertTrue(g.isAdjacent(0,1));
    Assertions.assertFalse(g.isAdjacent(0,0));
  }
}
