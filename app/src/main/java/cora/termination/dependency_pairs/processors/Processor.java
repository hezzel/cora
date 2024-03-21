package cora.termination.dependency_pairs.processors;

import cora.termination.dependency_pairs.Problem;

public interface Processor {
  boolean isApplicable(Problem dpp);
  ProcessorProofObject processDPP(Problem dpp);
}
