package cora.rwinduction.engine.deduction;

import charlie.util.either.Either;
import charlie.util.either.Left;
import charlie.util.either.Right;
import cora.rwinduction.engine.data.ProofState;

abstract class DeductionAbstractRule {

  /**
   * Let us assume given a proof state {@code (E, H)}.
   * In order to apply a deduction rule {@code D} on an equation in {@code E},
   * we need to first check that all the requirements for the applicability of {@code D} are met.
   *
   * @return returns an {@code Either<String, Bool>} object such that
   * <li> if the rule can be applied, it returns {@code Right<Boolean>(true)}; otherwise,</li>
   * <li> this method should return a value of type {@code Left<String} in case the rule cannot
   * be applied (this string should be a human-readable explanation of why this rule
   * cannot be applied).
   * Moreover, if the rule cannot be applied but no explanation is required,
   * it returns {@code Right<Boolean>} with {@code false}.
   * </li>
   *
   * @apiNote Whenever a rule cannot be applied,
   * implementors of this method are encouraged to always return {@code Left<String> reason}.
   * This will make it easier for the end user to understand how to fix the mistake and call the
   * deduction rule again.
   * <p> This API will always assume that if no reason is provided, none is needed.</p>
   * <p> See {@link Either} for more details on this type.</p>
   */
  abstract <T extends DeductionArguments> Either<String, Boolean> isApplicable(T args);

  //TODO implement documentation
  protected abstract <T extends DeductionArguments> Either<String, ProofState> ruleLogic(T args);

  //TODO implement documentation
  public final <T extends DeductionArguments> Either<String, ProofState> applyRule(T args) {

    Either<String, Boolean> result = isApplicable(args);

    return switch (result) {
      case Left<String, Boolean> reason -> new Left<>(reason.value());
      case Right<String, Boolean> res -> {
        if (res.value()) {
          yield ruleLogic(args);
        } else {
          yield new Left<>("This rule cannot be applied with the provided arguments.");
        }
      }
    };
  }
}
