package cora.termination.dependency_pairs;

import charlie.trs.TRS;
import charlie.trs.TrsProperties.*;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.termination.TerminationAnswer;
import cora.termination.dependency_pairs.processors.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import static cora.termination.TerminationAnswer.*;

public class DPFramework {
  private ProofObject isTRSApplicable(TRS trs) {
    if (!trs.verifyProperties(Level.APPLICATIVE, Constrained.YES, Products.DISALLOWED,
                              Lhs.PATTERN, Root.FUNCTION)) {
      return new ProofObject() {
        public Boolean queryAnswer() { return false; }
        public void justify(OutputModule o) {
          o.println("For now, static dependency pairs can only be applied on applicative " +
                    "systems without tuples, where the left-hand sides of rules are patterns " +
                    "and their root always a non-theory symbol.");
        }
      };
    }
    AccessibilityChecker checker = new AccessibilityChecker(trs);
    return checker.checkAccessibility();
  }

  private static Problem computeInitialProblem(TRS trs) {
    return DPGenerator.generateProblemFromTrs(trs);
  }

  public DPProofObject proveTermination(TRS trs) {
    ProofObject appl = isTRSApplicable(trs);
    if (!((Boolean)appl.queryAnswer()).booleanValue()) return new DPProofObject(appl);

    ReachabilityProcessor reachProcessor = new ReachabilityProcessor();
    GraphProcessor   graphProcessor   = new GraphProcessor();
    SubtermProcessor subtermProcessor = new SubtermProcessor();
    KasperProcessor  kasperProcessor  = new KasperProcessor();
    TheoryArgumentsProcessor targProcessor = new TheoryArgumentsProcessor();
    SplittingProcessor splitProcessor = new SplittingProcessor();
    List<Processor> proclist =
      List.of(graphProcessor, subtermProcessor, targProcessor, kasperProcessor);

    Problem initialProblem = DPFramework.computeInitialProblem(trs);
    DPProofObject ret = new DPProofObject(appl, initialProblem);

    // we start with the processors that preserve the "public" nature of a chain
    ProcessorProofObject tmp;
    tmp = splitProcessor.transform(initialProblem);
    if (tmp.applicable()) { ret.addProcessorProof(tmp); initialProblem = tmp.queryOutput(); }
    tmp = targProcessor.transform(initialProblem);
    if (tmp.applicable()) { ret.addProcessorProof(tmp); initialProblem = tmp.queryOutput(); }
    tmp = reachProcessor.transform(initialProblem);
    if (tmp.applicable()) { ret.addProcessorProof(tmp); initialProblem = tmp.queryOutput(); }

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
        ProcessorProofObject ppo = proc.processDPP(p);
        if (ppo.applicable()) {
          toBeSolved.addAll(ppo.queryResults());
          ret.addProcessorProof(ppo);
          success = true;
          break;
        }
      }
      if (!success) {
        // Here the problem failed in all processors and couldn't be solved
        ret.setFailedProof(p);
        return ret;
      }
    }
    ret.setTerminating();
    return ret;
  }
}

