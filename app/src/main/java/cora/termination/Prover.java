package cora.termination;

import cora.utils.Pair;
import cora.trs.TRS;

import java.util.Optional;

public interface Prover {

  Boolean isTRSApplicable(TRS trs);

  Pair<TerminationAnswer, Optional<String>> proveTermination(TRS trs);

}
