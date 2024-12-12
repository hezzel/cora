/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rwinduction.engine;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Stack;
import charlie.exceptions.NullStorageException;
import charlie.util.FixedList;
import charlie.terms.Renaming;
import charlie.terms.TermPrinter;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.util.Pair;
import cora.io.OutputModule;

/**
 * A PartialProof keeps track of the current proof state, the history, and all other information
 * that is not contained in a proof state but is relevant for the overall proof process.  If the
 * current state of a PartialProof is final, then a partial proof in fact represents a full proof.
 *
 * A partial proof is mutable, and can for instance have new proof states added to it.
 */
public class PartialProof {
  private final TRS _trs;
  private final ArrayList<String> _ruleNames;
  private final ArrayList<Renaming> _ruleRenamings;
  private final HashMap<String,Integer> _nameToRule;

  private final Stack<ProofState> _previousStates = new Stack<ProofState>();
  private final Stack<String> _previousCommands = new Stack<String>();
  private final Stack<ProofState> _futureStates = new Stack<ProofState>();
  private final Stack<String> _futureCommands = new Stack<String>();

  private ProofState _currentState;
  private boolean _aborted;

  /**
   * Constructor: sets up a partial proof empty history, the proof state (initialEquations,ø,ø),
   * and rules from the given TRS, with Renamings built by the given term printer.
   */
  public PartialProof(TRS initialSystem, FixedList<Equation> initialEquations, TermPrinter tp) {
    if (initialSystem == null) throw new NullStorageException("PartialProof", "initial TRS");
    if (initialEquations == null) throw new NullStorageException("PartialProof", "initial eqs");
    _trs = initialSystem;
    _currentState = new ProofState(initialEquations);
    int n = initialSystem.queryRuleCount();
    _ruleNames = new ArrayList<String>(n);
    _ruleRenamings = new ArrayList<Renaming>(n);
    _nameToRule = new HashMap<String,Integer>(n);
    for (int i = 0; i < initialSystem.queryRuleCount(); i++) {
      Rule rule = initialSystem.queryRule(i);
      Renaming renaming =
        tp.generateUniqueNaming(rule.queryLeftSide(), rule.queryRightSide(), rule.queryConstraint());
      String name = "R" + (i+1);
      _ruleNames.add(name);
      _nameToRule.put(name, i);
      _ruleRenamings.add(renaming);
    }
  }

  public TRS getTRS() {
    return _trs;
  }

  public String getRuleName(int index) {
    return _ruleNames.get(index);
  }

  public Rule getRule(String name) {
    return _trs.queryRule(_nameToRule.get(name));
  }

  public Renaming getRenaming(String ruleName) {
    return _ruleRenamings.get(_nameToRule.get(ruleName));
  }

  /**
   * Returns the current proof state of the prover.
   * The current proof state is not altered.
   */
  public ProofState getProofState() {
    return _currentState;
  }

  /**
   * Returns a list with all the commands needed to get from the initial state to the current state.
   * Note that while this list is mutable, altering it will not affect the current PartialProof.
   */
  public ArrayList<String> getCommandHistory() {
    return new ArrayList<String>(_previousCommands);
  }

  /**
   * This returns true if either the current state is final, or the partial proof has been forcibly
   * marked as aborted.
   */
  public boolean isDone() {
    return _aborted || _currentState.isFinalState();
  }

  /**
   * This marks the PartialProof as "aborted": the proof process should end, whether or not we are
   * in a final state.
   */
  public void abort() {
    _aborted = true;
  }

  /**
   * Sets the given proof state as current, and marks that we used the given commandLiteral to get
   * there from the previous state.
   */
  public void addProofStep(ProofState proofState, String commandLiteral) {
    _previousStates.push(_currentState);
    _previousCommands.push(commandLiteral);
    _currentState = proofState;
    _futureStates.clear();
    _futureCommands.clear();
  }

  /**
   * This undoes the last proof step, and restores the state we had before.  Returns false if there
   * is nothing to undo.
   */
  public boolean undoProofStep() {
    if (_previousStates.isEmpty()) return false;
    _futureStates.push(_currentState);
    _futureCommands.push(_previousCommands.pop());
    _currentState = _previousStates.pop();
    return true;
  }

  /**
   * If we just performed an undo, then this undoes the undoing.  Returns false if there is nothing
   * to redo.
   */
  public boolean redoProofStep() {
    if (_futureStates.isEmpty()) return false;
    _previousStates.push(_currentState);
    _previousCommands.push(_futureCommands.pop());
    _currentState = _futureStates.pop();
    return true;
  }
}
