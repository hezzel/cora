package cora.termination.dependency_pairs.processors;

import cora.termination.dependency_pairs.Problem;

public interface Processor {
  /**
   * Returns false if we shouldn't even try to apply the processor on the given DP problem, for
   * example because it's a processor for unconstrained systems and the given problem has
   * constraints.
   */
  boolean isApplicable(Problem dpp);

  /**
   * Executes the processor on the given DP, and returns a proof object explaining either success
   * or failure.
   */
  ProcessorProofObject processDPP(Problem dpp);
}
