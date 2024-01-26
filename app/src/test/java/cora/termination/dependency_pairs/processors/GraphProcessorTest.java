package cora.termination.dependency_pairs.processors;

import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.certification.Informal;
import cora.terms.Term;
import cora.terms.TermFactory;
import cora.types.TypeFactory;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

class GraphProcessorTest {

  List<DP> createDPExamples() {
    Term a = TermFactory.createConstant("a", TypeFactory.intSort);
    Term b = TermFactory.createConstant("b", TypeFactory.intSort);
    Term c = TermFactory.createConstant("c", TypeFactory.intSort);

    DP dp1 = new DP(a, a);
    DP dp2 = new DP(a,b);
    DP dp3 = new DP(b,c);
    DP dp4 = new DP(c,b);

    return new ArrayList<>(List.of(dp1, dp2, dp3, dp4));
  }

  @Test
  void processTest() {
    List<DP> dps = this.createDPExamples();
    System.out.println("Total list of DPs: " + dps);

    Problem p = new Problem(dps);
    GraphProcessor proc = new GraphProcessor();

    List<Problem> pp = proc.computeAllSubproblems(p);

    System.out.println("Number of problems that came from nontrivial SCCs: " + pp.size());
    System.out.println("The subgraph generated from each SCC...");
    for(Problem g : pp) {
      g.getGraph().ifPresent(System.out::println);
    }
  }

  @Test
  void isApplicable() {
  }

  @Test
  void processDPP() {

    Informal a = Informal.getInstance();
    a.addProofStep("A");
    Informal b = Informal.getInstance();
    b.addProofStep("B");
    System.out.println(b.getInformalProof());

  }
}
