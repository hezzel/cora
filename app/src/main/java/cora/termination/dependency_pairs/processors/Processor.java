package cora.termination.dependency_pairs.processors;

import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;

import java.util.List;
import java.util.Optional;

public interface Processor {

  // check whether a given processor can be applied to a DP problem
  default boolean isApplicable(Problem dpp) {
    return false;
  }

  Optional<List<Problem>> processDPP(Problem dpp);
}
