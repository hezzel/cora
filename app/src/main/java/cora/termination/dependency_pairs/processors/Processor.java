package cora.termination.dependency_pairs.processors;

import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;

import java.util.List;

public interface Processor {

//  check whether a given processor can be applied to a DP problem
  boolean isApplicable(DP dp);

  List<Problem> processDPP(Problem dpp);
}
