package cora.termination;
import cora.utils.Pair;

public class Handler {
  private final Request _proofRequest;

  public enum Answer { YES, NO, MAYBE, NOT_APPLICABLE }

  Handler(Request request) {
    _proofRequest = request;
  }

  private Pair<Answer, String> buildMaybeAnswer() {
    return new Pair<>(Answer.MAYBE, "");
  }

  public Pair<Answer, String> getResponse() {
    return switch (_proofRequest.get_requestedTechnique()) {
        case HORPO -> {
          System.out.println("Chosen horpo.");
          yield buildMaybeAnswer();
        }
        case DP -> {
          yield buildMaybeAnswer();
        }
        default -> {
          System.out.println("No termination proof can be done.");
          yield buildMaybeAnswer();
        }
    };
  }
}
