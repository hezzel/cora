package cora.termination.dependency_pairs;

import cora.rewriting.TRS;
import cora.termination.Handler.Answer;
import cora.termination.Prover;
import cora.termination.dependency_pairs.certification.Informal;
import cora.termination.dependency_pairs.processors.GraphProcessor;
import cora.termination.dependency_pairs.processors.KasperProcessor;
import cora.termination.dependency_pairs.processors.SubtermProcessor;
import cora.utils.Pair;
import org.checkerframework.checker.units.qual.K;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Stack;

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
    return null;
  }

  @Override
  public Pair< Answer, Optional<String> > proveTermination(TRS trs) {
    if (isTRSApplicable(trs)) {
      GraphProcessor   graphProcesor    = new GraphProcessor();
      SubtermProcessor subtermProcessor = new SubtermProcessor();
      KasperProcessor  kasperProcessor  = new KasperProcessor();

      Problem initialProblem = DPFramework.computeInitialProblem(trs);

      // First, we compute the graph of the initial problem.
      Optional<List<Problem>> dppsFromGraph = graphProcesor.processDPP(initialProblem);

      if (dppsFromGraph.isEmpty()) {
        return new Pair<>(MAYBE, Optional.of(""));
      } else {
        List<Problem> toBeSolved = dppsFromGraph.get();
        List<Problem> failedInAll = new ArrayList<>();

        // Trying to solve each problem in toBeSolved
        while (!toBeSolved.isEmpty()) {
          // Get the first problem in the list of problems to be solved
          Problem p = toBeSolved.getFirst();

          // Try subterm processor
          Optional<List<Problem>> subterm = subtermProcessor.processDPP(p);
          if (subterm.isPresent()) {
            toBeSolved.removeFirst();
            toBeSolved.addAll(subterm.get());
          } else {
            // Try kasper's processor
            Optional<List<Problem>> kasper = kasperProcessor.processDPP(p);
            if (kasper.isPresent()) {
              toBeSolved.removeFirst();
              toBeSolved.addAll(kasper.get());
            } else {
              // Here the problem failed in all processors and couldn't be solved
              return new Pair<>(MAYBE, Optional.of(""));
            }
          }
        }
        return new Pair<>(YES, Optional.of(Informal.getInstance().getInformalProof()));
      }
    } else {
      return new Pair<>(MAYBE, Optional.empty());
    }
  }
}
