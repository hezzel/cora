package cora.rwinduction.engine.data;

import charlie.terms.Renaming;
import charlie.trs.Rule;
import charlie.trs.TRS;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import cora.io.OutputModule;
import java.util.Objects;
import java.util.Stack;

public class ProverContext {

  private final TRS _initialSystem;
  private final ImmutableMap<Integer, Renaming> _ruleRenamings;
  private final OutputModule _outputModule;

  private final String _initializeCommandName = "Proof.";
  private final String _endProofCommandName = "Qed.";


  private final Stack<ProofState> _proofStates = new Stack<>();
  private final Stack<String> _commandLiterals = new Stack<>();

  private final Stack<ProofState> _redoProofStateCache = new Stack<>();
  private final Stack<String>     _redoCmdLiteralsCache = new Stack<>();


  private static ImmutableMap<Integer, Renaming> genRuleRenaming(TRS trs, OutputModule outputModule) {
    ImmutableMap.Builder<Integer, Renaming> builder = ImmutableMap.builder();
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      Rule rule = trs.queryRule(i);
      Renaming renaming = outputModule
        .queryTermPrinter()
        .generateUniqueNaming(rule.queryLeftSide(), rule.queryRightSide(), rule.queryConstraint());
      builder.put(i, renaming);
    }
    return builder.build();
  }

  public ProverContext(TRS initialSystem,
                       ImmutableList<Equation> initialEquations,
                       OutputModule outputModule) {
    Objects.requireNonNull(initialSystem);
    Objects.requireNonNull(initialEquations);
    Objects.requireNonNull(outputModule);

    _initialSystem = initialSystem;
    _outputModule = outputModule;
    _ruleRenamings = genRuleRenaming(_initialSystem, _outputModule);

    _proofStates.push(ProofState.createInitialState(_initialSystem, initialEquations));
    _commandLiterals.push(_initializeCommandName);
  }

  public Renaming getRuleRenaming(Integer ruleIndex) {return _ruleRenamings.get(ruleIndex); }

  public OutputModule getOutputModule() { return _outputModule; }

  /**
   * Returns the current proof state of the prover.
   * The current proof state is not altered.
   */
  public ProofState getProofState() { return _proofStates.peek(); }


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
