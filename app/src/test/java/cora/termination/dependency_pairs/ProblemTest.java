package cora.termination.dependency_pairs;

import static org.junit.jupiter.api.Assertions.*;

import cora.data.digraph.Digraph;
import cora.exceptions.IllegalArgumentError;
import cora.exceptions.NullInitialisationError;
import cora.termination.dependency_pairs.processors.GraphProcessor;
import cora.terms.Term;
import cora.terms.TermFactory;
import cora.types.Type;
import cora.types.TypeFactory;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

class ProblemTest {

//  List<DP> createDPExamples() {
//    Term a = TermFactory.createConstant("a", TypeFactory.intSort);
//    Term b = TermFactory.createConstant("b", TypeFactory.intSort);
//    Term c = TermFactory.createConstant("a", TypeFactory.intSort);
//
//    DP dp1 = new DP(a, a);
//    DP dp2 = new DP(a,b);
//    DP dp3 = new DP(a,c);
//
//    return new ArrayList<>(List.of(dp1, dp2, dp3));
//  }


//  @Test
//  void testProblemCreation() {
//    List<DP> dp = this.createDPExamples();
//    Problem p = new Problem(this.createDPExamples(), new Digraph(3));
//
//    Assertions.assertThrows(NullInitialisationError.class, () -> {
//      new Problem(null);
//    });
//
//    Assertions.assertThrows(NullInitialisationError.class, () -> {
//      new Problem(this.createDPExamples(), null);
//    });
//
//    Assertions.assertThrows(NullInitialisationError.class, () -> {
//      new Problem(null, new Digraph(0));
//    });
//
//    Assertions.assertThrows(IllegalArgumentError.class, () -> {
//      new Problem(dp, new Digraph(0));
//    });
//  }

}
