package cora.rwinduction.engine;

import java.util.Optional;
import java.util.function.BiFunction;

abstract class DeductionRule {

  /**
   * Let us assume given a proof state {@code (E, H)}.
   * In order to apply a deduction rule {@code D} on an equation in E,
   * we need to first check that all the requirements for the applicability of {@code D} are met.
   *
   * @param proofState the given proof state, of shape {@code (E, H)}
   * @param equationIndex the index of an equation {@code s = t [c]} in E.
   * @return {@code true} if the implemented rule can be applied and {@code false} otherwise.
   */
  boolean isApplicable(ProofState proofState, int equationIndex) {
    return false;
  }

  abstract ProofState ruleLogic(ProofState proofState, int equationIndex);

  final Optional<ProofState> applyRule(ProofState proofState, int equationIndex) {
    if (this.isApplicable(proofState, equationIndex))
      return Optional.of(ruleLogic(proofState, equationIndex));
    else
      return Optional.empty();
  }
}
