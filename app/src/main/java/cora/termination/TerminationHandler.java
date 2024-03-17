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
    if (!Horpo.applicable(trs)) return new ProofObject() {
      public Object queryAnswer() { return TerminationAnswer.NOT_APPLICABLE; }
      public void justify(OutputModule om) { }
    };
    return Horpo.run(trs);
  }
  /*
  private Pair<Answer, Optional<String>> buildMaybeAnswer() {
    return new Pair<>(Answer.MAYBE, Optional.empty());
  }

  public Pair<Answer, Optional<String>> getResponse() {
    return switch (_proofRequest.getRequestedTechnique()) {
        case HORPO -> {
          System.out.println("Chosen horpo.");
          yield buildMaybeAnswer();
        }
        case DP -> {
          DPFramework dpF = new DPFramework();
          yield dpF.proveTermination(_proofRequest.getTRS());
        }
        default -> {
          System.out.println("No termination proof can be done.");
          yield new Pair<>(Answer.NOT_APPLICABLE, Optional.empty());
        }
    };
  }
  */
}
