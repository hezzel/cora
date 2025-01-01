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
import cora.io.ParseableTermPrinter;

/**
 * A PartialProof keeps track of the current proof state, the proof context, and the history.
 * If the current state of a PartialProof is final, then a partial proof in fact represents a full
 * proof.
 *
 * A partial proof is mutable, and can for instance have new proof states added to it.
 */
public class PartialProof {
  private final ProofContext _pcontext;
  private final Stack<ProofState> _previousStates = new Stack<ProofState>();
  private final Stack<ProofState> _futureStates = new Stack<ProofState>();
  private final Stack<DeductionStep> _previousCommands = new Stack<DeductionStep>();
  private final Stack<DeductionStep> _futureCommands = new Stack<DeductionStep>();

  private ProofState _currentState;
  private boolean _aborted;

  /**
   * Constructor: sets up a partial proof with empty history, the proof state
   * (initialEquations,ø,ø), and rules from the given TRS, with Renamings built by the given term
   * printer.
   */
  public PartialProof(TRS initialSystem, FixedList<EquationContext> initialEquations,
                      TermPrinter tp) {
    if (initialEquations == null) throw new NullStorageException("PartialProof", "initial eqs");
    _pcontext = new ProofContext(initialSystem, tp);
    _currentState = new ProofState(initialEquations);
    _aborted = false;
  }

  /**
   * Returns the fixed data that is not contained in a proof state, but also relevant to the
   * proof process.
   */
  public ProofContext getContext() {
    return _pcontext;
  }

  /**
   * Returns the current proof state of the prover.
   * The current proof state is not altered.
   */
  public ProofState getProofState() {
    return _currentState;
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
   * Sets the given proof state as current, and marks that we used the given deduction step to get
   * there from the previous state.
   */
  public void addProofStep(ProofState proofState, DeductionStep step) {
    _previousStates.push(_currentState);
    _previousCommands.push(step);
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

  /**
   * Returns a list with all the commands needed to get from the initial state to the current state.
   * Note that while this list is mutable, altering it will not affect the current PartialProof.
   */
  public ArrayList<String> getCommandHistory() {
    ParseableTermPrinter printer =
      new ParseableTermPrinter(_pcontext.getTRS().queryFunctionSymbolNames());
    ArrayList<String> ret = new ArrayList<String>(_previousCommands.size());
    for (DeductionStep step : _previousCommands) {
      ret.add(step.commandDescription(printer));
    }
    return ret;
  }

  /** Returns a list with all the deduction steps used to get to the current state. */
  public ArrayList<DeductionStep> getDeductionHistory() {
    return new ArrayList<DeductionStep>(_previousCommands);
  }
}

