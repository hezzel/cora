package cora.rwinduction.engine;


final class SimplifyRule extends DeductionRule {

  /**
   * @param args
   * @param <T>
   * @return
   */
  @Override
  <T extends RuleArguments> boolean isApplicable(T args) {
    return false;
  }

  /**
   * @param args
   * @param <T>
   * @return
   */
  @Override
  protected <T extends RuleArguments> ProofState ruleLogic(T args) {
    return null;
  }

}
