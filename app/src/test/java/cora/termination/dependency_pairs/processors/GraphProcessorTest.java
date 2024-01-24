package cora.termination.dependency_pairs.processors;

import cora.data.digraph.Digraph;
import cora.data.digraph.SCC;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import cora.terms.Term;
import cora.terms.TermFactory;
import cora.types.TypeFactory;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class GraphProcessorTest {

  List<DP> createDPExamples() {
    Term a = TermFactory.createConstant("a", TypeFactory.intSort);
    Term b = TermFactory.createConstant("b", TypeFactory.intSort);
    Term c = TermFactory.createConstant("a", TypeFactory.intSort);

    DP dp1 = new DP(a, a);
    DP dp2 = new DP(a,b);
    DP dp3 = new DP(a,c);

    return new ArrayList<>(List.of(dp1, dp2, dp3));
  }

  @Test
  void processTest() {
    List<DP> dps = this.createDPExamples();

    Problem p = new Problem(dps);
    GraphProcessor proc = new GraphProcessor();

    // Digraph g = proc.problemToGraph(p);
    // System.out.println(g);
    // SCC scc = new SCC(g);
    // System.out.println(scc);
    List<Problem> pp = proc.computeNewAllSubproblems(p);

    System.out.println("Number of generated subproblems: " + pp.size());

    System.out.println(pp.getFirst());
    pp.getFirst().getGraph().ifPresent(System.out::println);
  }

  @Test
  void isApplicable() {
  }

  @Test
  void processDPP() {
  }
}
