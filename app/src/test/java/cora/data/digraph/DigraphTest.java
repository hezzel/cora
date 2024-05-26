package cora.data.digraph;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import java.util.List;
import java.util.Set;

import charlie.exceptions.IndexingError;

class DigraphTest {
  private Digraph createExampleGraph() {
    Digraph g = new Digraph(4);
    g.addEdge(0, 1);
    g.addEdge(0,1);
    g.addEdge(0, 2);
    g.addEdge(1, 0);
    g.addEdge(1, 2);
    g.addEdge(2, 1);
    return g;
  }

  @Test
  public void testBasicGraph() {
    Digraph g = createExampleGraph();
    assertTrue(g.getNumberOfVertices() == 4);
    assertTrue(g.getNumberOfEdges() == 5);
    assertTrue(g.isAdjacent(0, 2));
    assertFalse(g.isAdjacent(2, 0));
  }

  @Test
  public void testAddingAndRemoving() {
    Digraph g = createExampleGraph();
    assertTrue(g.toString().equals(
      "0 |-> [1, 2]\n" +
      "1 |-> [0, 2]\n" +
      "2 |-> [1]\n" +
      "3 |-> []\n"));
    g.removeEdge(1, 0);
    g.removeEdge(2, 1);
    g.addEdge(1, 0);
    g.addEdge(3, 2);
    g.addVertex();
    g.addEdge(3, 4);
    assertTrue(g.getNumberOfVertices() == 5);
    assertTrue(g.getNumberOfEdges() == 6);
    assertFalse(g.isAdjacent(2, 1));
    assertTrue(g.isAdjacent(1, 0));
    assertTrue(g.isAdjacent(3, 4));
    assertTrue(g.toString().equals(
      "0 |-> [1, 2]\n" +
      "1 |-> [0, 2]\n" +
      "2 |-> []\n" +
      "3 |-> [2, 4]\n" +
      "4 |-> []\n"));
  }

  @Test
  public void testSubgraph() {
    Digraph g = createExampleGraph();
    g.addEdge(0, 3);
    Digraph sub = g.getSubgraph(List.of(1,3,0));
    assertTrue(sub.toString().equals(
      "0 |-> [2]\n" +
      "1 |-> []\n" +
      "2 |-> [0, 1]\n"));
  }

  @Test
  public void testNeighbours() {
    Digraph g = createExampleGraph();
    Set<Integer> n0 = g.getNeighbours(0);
    Set<Integer> n3 = g.getNeighbours(3);
    assertTrue(n0.size() == 2);
    assertTrue(n0.contains(1));
    assertTrue(n0.contains(2));
    assertTrue(n3.size() == 0);
    // can't edit the neighbours list from here!
    assertThrows(UnsupportedOperationException.class, () -> n0.remove(1));
  }

  @Test
  void testDigraphNegativeSizeCreation() {
    Assertions.assertThrows(IllegalArgumentException.class, () -> {
      Digraph g = new Digraph(-1);
    });
  }

  @Test
  void testAddEdgeToEmptyDigraph() {
    Assertions.assertThrows(IndexingError.class, () -> {
      Digraph g = new Digraph(0);
      g.addEdge(0,0);
    });
  }

  @Test
  void testAddDuplicatedEdge() {
    Digraph g = new Digraph(3);
    g.addEdge(0,1);
    g.addEdge(0,1);
    Assertions.assertEquals(g.getNumberOfEdges(), 1);
  }

  @Test
  void tesAddingOutOfBoundsOrigin() {
    Assertions.assertThrows(IndexingError.class, () -> {
      Digraph g = new Digraph(3);
      g.addEdge(3,0);
    });
  }

  @Test
  void testAddingOutOfBoundsDestination() {
    Assertions.assertThrows(IndexingError.class, () -> {
      Digraph g = new Digraph(3);
      g.addEdge(0, 3);
    });
  }
}
