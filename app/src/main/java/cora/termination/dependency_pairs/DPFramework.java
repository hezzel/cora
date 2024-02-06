package cora.termination.dependency_pairs;

import cora.rewriting.TRS;
import cora.termination.Handler.Answer;
import cora.termination.Prover;
import cora.termination.dependency_pairs.processors.GraphProcessor;
import cora.termination.dependency_pairs.processors.KasperProcessor;
import cora.termination.dependency_pairs.processors.SubtermProcessor;
import cora.utils.Pair;
import org.checkerframework.checker.units.qual.K;

import java.util.List;
import java.util.Optional;

import static cora.termination.Handler.Answer.*;

public class DPFramework implements Prover {

  @Override
  public Boolean isTRSApplicable(TRS trs) {
    return true;
  }

  private static Problem computeInitialProblem(TRS trs) {
    return DPGenerator.generateProblemFromTrs(trs);
  }

  private static List<Problem> terminationStrategy(List<Problem> dpps) {
    while (!dpps.isEmpty()) {
      Problem p = dpps.getFirst();
      dpps.removeFirst();
      // apply the processors to P
    }
    return List.of();
  }

  @Override
  public Pair< Answer, Optional<String> > proveTermination(TRS trs) {
    if (isTRSApplicable(trs)) {
      GraphProcessor graphProcesor = new GraphProcessor();
      Problem initialProblem       = DPFramework.computeInitialProblem(trs);
      List<Problem> dppsFromProblem   = graphProcesor.processDPP(initialProblem);

//      // Executing the subterm processor for testing
//      System.out.println("Execute Subterm Processor for testing...");
//      SubtermProcessor subProc = new SubtermProcessor();
//      List<Problem> ret = subProc.processDPP(dppsFromProblem.getFirst());
//      System.out.println("Final result of the processor: " + ret);

      // Now low-level testing of KasperProcessor
      System.out.println("Executing Kasper Processor for Testing");
      KasperProcessor kasperProcessor = new KasperProcessor();
      List<Problem> ret = kasperProcessor.processDPP(dppsFromProblem.getFirst());

      // TODO For now, I am returning the same output because the DP framework is only running
      //  one processor at a time for debugging purposes only.
      if ( terminationStrategy(dppsFromProblem).isEmpty() ){
        return new Pair<>(MAYBE, Optional.of("Termination proover didn't run yet."));
      } else {
        return new Pair<>(MAYBE, Optional.of("Termination proover didn't run yet."));
      }

    } else {
      return new Pair<>(NOT_APPLICABLE, Optional.empty());
    }
  }
}
