package cora.termination.dependency_pairs;

import cora.rewriting.TRS;
import cora.termination.Handler.Answer;
import cora.termination.Prover;
import cora.termination.dependency_pairs.processors.GraphProcessor;
import cora.termination.dependency_pairs.processors.KasperProcessor;
import cora.utils.Pair;
import java.util.List;
import java.util.Optional;
import static cora.termination.Handler.Answer.*;

public class DPFramework implements Prover {

  @Override
  public Boolean isTRSApplicable(TRS trs) {
    AccessibilityChecker checker = new AccessibilityChecker(trs);
    return checker.checkAccessibility();
  }

  private static Problem computeInitialProblem(TRS trs) {
    return DPGenerator.generateProblemFromTrs(trs);
  }

  private static List<Problem> terminationStrategy(List<Problem> dpps) {
    while (!dpps.isEmpty()) {
      Problem p = dpps.getFirst();


      GraphProcessor graphProcessor = new GraphProcessor();
      graphProcessor.processDPP(p);

      dpps.removeFirst();
    }
    return List.of();
  }

  @Override
  public Pair< Answer, Optional<String> > proveTermination(TRS trs) {
    if (isTRSApplicable(trs)) {
      GraphProcessor graphProcesor = new GraphProcessor();
      Problem initialProblem       = DPFramework.computeInitialProblem(trs);
      List<Problem> dppsFromProblem =   graphProcesor.processDPP(initialProblem).get();

      // Now low-level testing of KasperProcessor
      System.out.println("Executing Kasper Processor for Testing");
      KasperProcessor kasperProcessor = new KasperProcessor();
      List<Problem> ret = kasperProcessor.processDPP(dppsFromProblem.getFirst()).get();

      // TODO For now, I am returning the same output because the DP framework is only running
      //  one processor at a time for debugging purposes only.
      if ( terminationStrategy(dppsFromProblem).isEmpty() ){
        return new Pair<>(MAYBE, Optional.of("Termination prover didn't run yet."));
      } else {
        return new Pair<>(MAYBE, Optional.of("Termination prover didn't run yet."));
      }

    } else {
      return new Pair<>(MAYBE, Optional.empty());
    }
  }
}
