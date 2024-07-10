package cora.rwinduction.engine.data;

import charlie.trs.TRS;

import java.util.Objects;
import java.util.Stack;

public class ProverContext {

  private final TRS _initialSystem;

  private final String _initializeCommandName = "Proof.";
  private final String _endProofCommandName = "Qed.";


  private final Stack<ProofState> _proofStates = new Stack<>();
  private final Stack<String> _commandLiterals = new Stack<>();

  private final Stack<ProofState> _redoProofStateCache = new Stack<>();
  private final Stack<String>     _redoCmdLiteralsCache = new Stack<>();

  public ProverContext(TRS initialSystem) {
    Objects.requireNonNull(initialSystem);
    _initialSystem = initialSystem;

    _proofStates.push(ProofState.createInitialState(_initialSystem));
    _commandLiterals.push(_initializeCommandName);
  }

  /**
   * Returns the current proof state of the prover. The current proof state is not altered.
   */
  public ProofState getProofState() {
    return _proofStates.peek();
  }

  public void addProofStep(ProofState proofState, String commandLiteral) {
    _proofStates.push(proofState);
    _commandLiterals.push(commandLiteral);
  }

  public void undoProofStep() {
    _redoProofStateCache.push(_proofStates.pop());
    _redoCmdLiteralsCache.push(_commandLiterals.pop());
  }

  public void redoProofStep() {
    _proofStates.push(_redoProofStateCache.pop());
    _commandLiterals.push(_redoCmdLiteralsCache.pop());
  }

}
