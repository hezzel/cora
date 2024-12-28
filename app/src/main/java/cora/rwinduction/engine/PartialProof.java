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
 * A PartialProof keeps track of the current proof state, the history, and all other information
 * that is not contained in a proof state but is relevant for the overall proof process.  If the
 * current state of a PartialProof is final, then a partial proof in fact represents a full proof.
 *
 * A partial proof is mutable, and can for instance have new proof states added to it.
 */
public class PartialProof {
  private final TRS _trs;
  private final ArrayList<String> _ruleNames = new ArrayList<String>();
  private final ArrayList<Renaming> _ruleRenamings = new ArrayList<Renaming>();
  private final HashMap<String,Integer> _nameToRule = new HashMap<String,Integer>();
  private final ParseableTermPrinter _printer;

  private record StateInformation(ProofState state, int firstFreeIndex) {}

  private final Stack<StateInformation> _previousStates = new Stack<StateInformation>();
  private final Stack<StateInformation> _futureStates = new Stack<StateInformation>();
  private final Stack<DeductionStep> _previousCommands = new Stack<DeductionStep>();
  private final Stack<DeductionStep> _futureCommands = new Stack<DeductionStep>();

  private ProofState _currentState;
  private int _firstAvailableIndex;
  private boolean _aborted;

  /**
   * Constructor: sets up a partial proof with empty history, the proof state
   * (initialEquations,ø,ø), and rules from the given TRS, with Renamings built by the given term
   * printer.
   */
  public PartialProof(TRS initialSystem, FixedList<Equation> initialEquations, TermPrinter tp) {
    if (initialSystem == null) throw new NullStorageException("PartialProof", "initial TRS");
    if (initialEquations == null) throw new NullStorageException("PartialProof", "initial eqs");
    _trs = initialSystem;
    _printer = new ParseableTermPrinter(initialSystem.queryFunctionSymbolNames());
    _currentState = new ProofState(initialEquations);
    _aborted = false;
    _firstAvailableIndex = _currentState.queryLargestIndex() + 1;
    int n = initialSystem.queryRuleCount();
    for (int i = 0; i < initialSystem.queryRuleCount(); i++) {
      Rule rule = initialSystem.queryRule(i);
      Renaming renaming =
        tp.generateUniqueNaming(rule.queryLeftSide(), rule.queryRightSide(), rule.queryConstraint());
      String name = "O" + (i+1);
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

  public boolean hasRule(String name) {
    return _nameToRule.containsKey(name);
  }

  public Rule getRule(String name) {
    Integer i = _nameToRule.get(name);
    if (i == null) return null;
    return _trs.queryRule(i);
  }

  public Renaming getRenaming(String ruleName) {
    Integer i = _nameToRule.get(ruleName);
    if (i == null) return null;
    return _ruleRenamings.get(i);
  }

  public int getFirstAvailableIndex() {
    return _firstAvailableIndex;
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
    int newindex = proofState.queryLargestIndex() + 1;
    if (newindex < _firstAvailableIndex) newindex = _firstAvailableIndex;
    _previousStates.push(new StateInformation(_currentState, _firstAvailableIndex));
    _previousCommands.push(step);
    _currentState = proofState;
    _firstAvailableIndex = newindex;
    _futureStates.clear();
    _futureCommands.clear();
  }

  /**
   * This undoes the last proof step, and restores the state we had before.  Returns false if there
   * is nothing to undo.
   */
  public boolean undoProofStep() {
    if (_previousStates.isEmpty()) return false;
    _futureStates.push(new StateInformation(_currentState, _firstAvailableIndex));
    _futureCommands.push(_previousCommands.pop());
    StateInformation si = _previousStates.pop();
    _currentState = si.state();
    _firstAvailableIndex = si.firstFreeIndex();
    return true;
  }

  /**
   * If we just performed an undo, then this undoes the undoing.  Returns false if there is nothing
   * to redo.
   */
  public boolean redoProofStep() {
    if (_futureStates.isEmpty()) return false;
    _previousStates.push(new StateInformation(_currentState, _firstAvailableIndex));
    _previousCommands.push(_futureCommands.pop());
    StateInformation si = _futureStates.pop();
    _currentState = si.state();
    _firstAvailableIndex = si.firstFreeIndex();
    return true;
  }

  /**
   * Returns a list with all the commands needed to get from the initial state to the current state.
   * Note that while this list is mutable, altering it will not affect the current PartialProof.
   */
  public ArrayList<String> getCommandHistory() {
    ParseableTermPrinter printer = new ParseableTermPrinter(_trs.queryFunctionSymbolNames());
    ArrayList<String> ret = new ArrayList<String>(_previousCommands.size());
    for (DeductionStep step : _previousCommands) {
      ret.add(step.commandDescription(printer));
    }
    return ret;
  }

  /** This prints an explanation of the proof state up until the current state. */
  public void explain(OutputModule module) {
    ProofState start = _previousStates.isEmpty() ? _currentState : _previousStates.get(0).state();
    module.println("We start the process with the following equations:");
    printEquations(module, start.getEquations());
    for (int i = 0; i < _previousCommands.size(); i++) {
      _previousCommands.get(i).explain(module);
      ProofState curr = _previousStates.get(i).state();
      ProofState next = i + 1 < _previousStates.size() ? _previousStates.get(i+1).state()
                                                       : _currentState;
      ArrayList<Equation> neweqs = getNewEquations(next, _previousStates.get(i).firstFreeIndex);
      if (neweqs.size() == 1) {
        module.println("This yields %a: %a", neweqs.get(0).getName(), neweqs.get(0));
      }
      else {
        module.println("This yields the following new equations:");
        printEquations(module, neweqs);
      }
    }
  }
  
  /**
   * Helper function for getNewEquation: returns all equations in the given proof state whose index
   * is at least [atleast].
   */
  private ArrayList<Equation> getNewEquations(ProofState state, int atleast) {
    ArrayList<Equation> ret = new ArrayList<Equation>();
    for (Equation eq : state.getEquations()) {
      if (eq.getIndex() >= atleast) ret.add(eq);
    }
    return ret;
  }

  /** Helper function for explain: prints the equations given by the given iterable. */
  private void printEquations(OutputModule module, Iterable<Equation> eqs) {
    module.startTable();
    for (Equation eq : eqs) {
      module.nextColumn("%a:", eq.getName());
      module.println("%a", eq);
    }
    module.endTable();
  }
}

