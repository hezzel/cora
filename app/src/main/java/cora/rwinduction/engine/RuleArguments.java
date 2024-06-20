package cora.rwinduction.engine;

import charlie.util.either.Either;
import charlie.util.either.Left;
import charlie.util.either.Right;

class RuleArguments {
  private final ProofState _proofState;
  protected final int _equationIndex;

  public enum EqSide {L, R}

  public RuleArguments(ProofState proofState, int ruleIndex) {
    _proofState = proofState;
    _equationIndex = ruleIndex;
  }

  public ProofState getProofState() {
    return _proofState;
  }

  public int getEquationIndex() {
    return _equationIndex;
  }

  Either<String, Boolean> checkEqBounds() {
    if (this.getEquationIndex() >= this.getProofState().getEquations().size()) {
      return new Left<>("The provided equation index, "
        + this.getEquationIndex() + ","
        + " is out of bounds. "
        + "Please choose another index. "
        + "It should be from 0 to " + (this.getProofState().getEquations().size() - 1) + ".");
    } else {
      return new Right<>(true);
    }
  }

}
