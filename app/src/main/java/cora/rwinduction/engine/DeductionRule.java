package cora.rwinduction.engine;

import java.util.Optional;

abstract class DeductionRule {

  /**
   * Let us assume given a proof state {@code (E, H)}.
   * In order to apply a deduction rule {@code D} on an equation in E,
   * we need to first check that all the requirements for the applicability of {@code D} are met.
   *
   * @return {@code true} if the implemented rule can be applied and {@code false} otherwise.
   *
   */
  abstract <T extends RuleArguments> boolean isApplicable(T args);

  protected abstract <T extends RuleArguments> ProofState ruleLogic(T args);

  final <T extends RuleArguments> Optional<ProofState> applyRule(T args) {
    if (this.isApplicable(args))
      return Optional.of(ruleLogic(args));
    else
      return Optional.empty();
  }
}
