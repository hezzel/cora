package cora.termination.dependency_pairs;

import cora.rewriting.TRS;
import cora.termination.Handler.Answer;
import cora.termination.Prover;
import cora.termination.dependency_pairs.processors.GraphProcessor;
import cora.utils.Pair;

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
      List<Problem> dpsFromGraph   = graphProcesor.processDPP(initialProblem);

      if ( terminationStrategy(dpsFromGraph).isEmpty() ){
        return new Pair<>(MAYBE, Optional.of("Termination proover didn't run yet."));
      } else {
        return new Pair<>(MAYBE, Optional.of("Termination proover didn't run yet."));
      }
    } else {
      return new Pair<>(NOT_APPLICABLE, Optional.empty());
    }
  }
}
