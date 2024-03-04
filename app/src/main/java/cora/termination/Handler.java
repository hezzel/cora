package cora.termination;

import cora.utils.Pair;
import cora.termination.dependency_pairs.DPFramework;

import java.util.Optional;

public class Handler {
  private final Request _proofRequest;

  public enum Answer { YES, NO, MAYBE, NOT_APPLICABLE }

  public Handler(Request request) {
    _proofRequest = request;
  }

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
}
