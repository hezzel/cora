package cora.termination;

import cora.utils.Pair;
import cora.trs.TRS;
import cora.termination.Handler.Answer;

import java.util.Optional;

public interface Prover {

  Boolean isTRSApplicable(TRS trs);

  Pair<Answer, Optional<String>> proveTermination(TRS trs);

}
