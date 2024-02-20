package cora.termination;

import cora.trs.TRS;
import cora.utils.Pair;
import cora.termination.Handler.Answer;

import java.util.Optional;

public interface Prover {

  default Boolean isTRSApplicable(TRS trs) {
    return false;
  }

  Pair<Answer, Optional<String>> proveTermination(TRS trs);

}
