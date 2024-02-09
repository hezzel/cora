package cora.termination.dependency_pairs;

import cora.rewriting.TRS;
import cora.termination.Handler.Answer;
import cora.termination.Prover;
import cora.termination.dependency_pairs.certification.Informal;
import cora.termination.dependency_pairs.processors.*;
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

  @Override
  public Pair< Answer, Optional<String> > proveTermination(TRS trs) {
    if (!isTRSApplicable(trs)) return new Pair<>(MAYBE, Optional.empty());

    GraphProcessor   graphProcessor    = new GraphProcessor();
    SubtermProcessor subtermProcessor = new SubtermProcessor();
    KasperProcessor  kasperProcessor  = new KasperProcessor();
    TheoryArgumentsProcessor targProcessor = new TheoryArgumentsProcessor();
    SplittingProcessor splitProcessor = new SplittingProcessor();
    List<Processor> proclist =
      List.of(graphProcessor, subtermProcessor, targProcessor, kasperProcessor);

    Informal.getInstance().addProofStep("We start by calculating the following Static Dependency Pairs:");

    Problem initialProblem = DPFramework.computeInitialProblem(trs);

    Informal.getInstance().addProofStep(initialProblem.toString());

    // we start with the processors that preserve the "public" nature of a chain
    initialProblem = splitProcessor.transform(initialProblem);
    initialProblem = targProcessor.transform(initialProblem);
    // TODO: reachability processor

    // At this point, we are looking for the absence of any chains, not just public chains;
    // this is handled by the main loop.

    ArrayList<Problem> toBeSolved = new ArrayList<Problem>();
    toBeSolved.add(initialProblem);
    // Trying to solve each problem in toBeSolved
    while (!toBeSolved.isEmpty()) {
      // Get the first problem in the list of problems to be solved
      Problem p = toBeSolved.removeFirst();
      boolean success = false;
      for (Processor proc : proclist) {
        Optional<List<Problem>> result = proc.processDPP(p);
        if (result.isPresent()) {
          toBeSolved.addAll(result.get());
          success = true;
          break;
        }
      }
      if (!success) {
        // Here the problem failed in all processors and couldn't be solved
        Informal.getInstance().addProofStep("***** No progress could be made on DP problem:\n" +
          p.toString());
        return new Pair<>(MAYBE, Optional.of(Informal.getInstance().getInformalProof()));
      }
    }
    return new Pair<>(YES, Optional.of(Informal.getInstance().getInformalProof()));
  }
}

