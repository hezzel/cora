package cora.rwinduction.engine.deduction;

import charlie.util.either.Either;
import charlie.util.either.Left;
import charlie.util.either.Right;
import cora.rwinduction.engine.data.ProofState;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;

public class DeductionArguments {
  private final ProofState _proofState;
  protected final int _equationIndex;

  public enum EqSide {L, R}

  public DeductionArguments(ProofState proofState, int ruleIndex) {
    _proofState = proofState;
    _equationIndex = ruleIndex;
  }

  public ProofState getProofState() {
    return _proofState;
  }

  /**
   * Returns the equation index which the rule should be applied to.
   */
  public final int getEquationIndex() {
    return _equationIndex;
  }

  @Contract(pure = true)
  private static @NotNull String getBoundsErrString(int ruleIndex, int maxIndex) {
    return "The provided equation index, "
      + ruleIndex + ","
      + " is out of bounds. "
      + "Please choose another index. "
      + "It should be from 0 to " + maxIndex + ".";
  }

  @Contract(" -> new")
  final @NotNull Either<String, Boolean> checkEqBounds() {
    if (this.getEquationIndex() >= this.getProofState().getEquations().size()) {
      return new Left<>(
        DeductionArguments.getBoundsErrString(
          this.getEquationIndex(),
          this.getProofState().getEquations().size() - 1
        ));
    } else {
      return new Right<>(true);
    }
  }

  @Contract("_ -> new")
  final @NotNull Either<String, Boolean> checkHypBounds(@NotNull int hypothesisIndex) {
    if (hypothesisIndex >= _proofState.getHypotheses().size()) {
      return new Left<>(
        DeductionArguments.getBoundsErrString(
          hypothesisIndex,
          _proofState.getHypotheses().size()
        )
      );
    } else {
      return new Right<>(true);
    }
  }
}
