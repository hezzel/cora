package cora.rwinduction.engine;

class RuleArguments {
  private final ProofState _proofState;
  protected final int _ruleIndex;

  public RuleArguments(ProofState proofState, int ruleIndex) {
    _proofState = proofState;
    _ruleIndex = ruleIndex;
  }

  public ProofState getProofState() {
    return _proofState;
  }

  public int getRuleIndex() {
    return _ruleIndex;
  }

}
