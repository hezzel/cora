package cora.termination;

import cora.utils.Pair;
import cora.trs.TRS;
import cora.io.ProofObject;
import cora.io.OutputModule;
import cora.termination.horpo.Horpo;
import cora.termination.dependency_pairs.DPFramework;

import java.util.Optional;

public class TerminationHandler {
  public static ProofObject proveHorpoTermination(TRS trs) {
    return Horpo.run(trs);
  }

  public static ProofObject proveTermination(TRS trs) {
    DPFramework dpF = new DPFramework();
    return dpF.proveTermination(trs);
  }
}
