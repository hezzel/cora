/**************************************************************************************************
 Copyright 2024--2025 Cynthia Kop

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

import java.util.List;

import charlie.util.FixedList;
import charlie.util.FixedSet;
import charlie.util.NullStorageException;
import charlie.trs.Rule;
import charlie.trs.TRS;

/**
 * The current state of the proof, consisting of the set of equation contexts that should be proved,
 * a set of induction hypotheses, and a set of ordering requirements.  We also keep track of which
 * equation indexes have been used so far, so we can always choose a fresh one for new equations.
 *
 * We handle completeness a bit different than in the paper, keeping track of indexes of equations
 * that are "incomplete".  A proof state is incomplete if and only if it has any incomplete
 * equations.  (The set of complete equations is guaranteed to be a subset of a previous complete
 * proof state.)
 *
 * @apiNote A ProofState is immutable.
 */
public class ProofState {
  private final FixedList<EquationContext> _equations;
  private final FixedList<Hypothesis> _hypotheses;
  private final FixedList<OrdReq> _ordering;
  private final FixedSet<Integer> _incomplete;
  private final int _lastUsedIndex;
  private final boolean _contradiction;

  /**
   * Instantiates a new proof state object with the following data:
   * @param initialEquations the list of equation contexts to be proved.
   * The proof state is marked as complete.
   */
  public ProofState(FixedList<EquationContext> initialEquations) {
    if (initialEquations == null) {
      throw new NullStorageException("ProofState", "initialEquations cannot be null");
    }

    _equations = initialEquations;
    _hypotheses = FixedList.of();
    _ordering = FixedList.of();
    _contradiction = false;

    int largest = 0;
    for (EquationContext eq : initialEquations) {
      if (eq.getIndex() > largest) largest = eq.getIndex();
    }
    _lastUsedIndex = largest;
    _incomplete = FixedSet.of();
  }

  /** Sets up a full proof state. */
  public ProofState(FixedList<EquationContext> equations, FixedList<Hypothesis> hypotheses,
                    FixedList<OrdReq> ordering, FixedSet<Integer> incomplete, int lastIndex) {
    if (equations == null || hypotheses == null || ordering == null) {
      throw new NullStorageException("ProofState", "one of the arguments in full constructor");
    }
    _equations = equations;
    _hypotheses = hypotheses;
    _ordering = ordering;
    _lastUsedIndex = lastIndex;
    _incomplete = incomplete;
    _contradiction = false;
  }

  /** Sets up the CONTRADICTION proof state . */
  private ProofState() {
    _equations = FixedList.of();
    _hypotheses = FixedList.of();
    _ordering = FixedList.of();
    _incomplete = FixedSet.of();
    _lastUsedIndex = 0;
    _contradiction = true;
  }

  public static ProofState getContradictionState() { return new ProofState(); }
 
  /** Returns the list of equation contexts in this proof state. */
  public FixedList<EquationContext> getEquations() {
    return _equations;
  }
 
  /** Returns the list of hypotheses in this proof state. */
  public FixedList<Hypothesis> getHypotheses() {
    return _hypotheses;
  }

  /** Returns the list of ordering requirements in this proof state. */
  public FixedList<OrdReq> getOrderingRequirements() {
    return _ordering;
  }

  /**
   * Returns the set of equations that cause this proof state to be incomplete.
   * (May be empty, in which case the proof state is complete.)
   */
  public FixedSet<Integer> getIncompleteEquations() {
    return _incomplete;
  }

  /** Returns the last used index in either this proof state or an ancestor. */
  public int getLastUsedIndex() {
    return _lastUsedIndex;
  }

  /**
   * Returns the equation context that's currently at the top of the list.
   * @throws IndexOutOfBoundException if there are no equations anymore.
   */
  public EquationContext getTopEquation() {
    return _equations.get(_equations.size()-1);
  }

  /** This returns the hypothesis with the given name if there is one, otherwise null. */
  public Hypothesis getHypothesisByName(String name) {
    for (Hypothesis h : _hypotheses) {
      if (h.getName().equals(name)) return h;
    }
    return null;
  }
  
  /**
   * Given a proof state and an equation context {@code context}, this method returns a new proof
   * state in which {@code context} is added to the set of equations.  Everything else is unaltered.
   * @param context the new equation context
   * @return the new proof state
   */
  public ProofState addEquation(EquationContext context) {
    int last = context.getIndex() > _lastUsedIndex ? context.getIndex() : _lastUsedIndex;
    FixedSet<Integer> inc = _incomplete;
    if (!_incomplete.isEmpty()) inc = inc.add(context.getIndex());
    return new ProofState(_equations.append(List.of(context)), _hypotheses, _ordering, inc, last);
  }

  /**
   * Given a proof state with E = {e1,...,en,e{n+1}} and an equation e', this method returns a proof
   * state in which E is updated to {e1,...,en,e'}.  Everything else is unaltered.
   * @param newData the new equation context
   * @return the new proof state
   */
  public ProofState replaceTopEquation(EquationContext newData) {
    return replaceTopEquation(List.of(newData));
  }

  /**
   * Given a proof state with E = {e1,...,en,e{n+1}} and a list of equations e'_1,...,e'_m, this
   * method returns a proof state in which E is updated to {e1,...,en,e'_1,...,e'_m}.  Everything
   * else is unaltered.  If the state is currently complete, the result state is also so; if the
   * state is currently incomplete, then all the new equations must be removed before it can be
   * marked as complete again.
   * @param newData the new equation context
   * @return the new proof state
   * @throws IndexOutOfBoundsException if the set of equations is empty (so there is no top proof
   *  state to replace
   */
  public ProofState replaceTopEquation(List<EquationContext> newData) {
    int last = _lastUsedIndex;
    if (_equations.isEmpty()) {
      throw new IndexOutOfBoundsException("ProofState::replaceTopEquation() called when the set " +
        "of equations is empty!");
    }
    FixedList.Builder<EquationContext> lst =
      new FixedList.Builder<EquationContext>(_equations.size() + newData.size() - 1);
    for (int i = 0; i < _equations.size()-1; i++) lst.add(_equations.get(i));
    for (EquationContext e : newData) {
      if (e.getIndex() > last) last = e.getIndex();
      lst.add(e);
    }
    FixedSet<Integer> inc = _incomplete;
    if (!inc.isEmpty()) {
      FixedSet.Builder<Integer> newinc = FixedSet.<Integer>treeBuilder();
      int replace = _equations.get(_equations.size()-1).getIndex();
      for (int k : _incomplete) { if (k != replace) newinc.add(k); }
      for (EquationContext ec : newData) { newinc.add(ec.getIndex()); }
      inc = newinc.build();
    }
    return new ProofState(lst.build(), _hypotheses, _ordering, inc, last);
  }

  /**
   * Given a proof state with E = {e1,...,en,e{n+1}}, this method returns a proof state in which E
   * updated to {e1,...,en}.  Everything else is unaltered.
   */
  public ProofState deleteTopEquation() {
    return replaceTopEquation(List.of());
  }

  /** Creates a copy of the current proof state with {@code hypothesis} added to the hypotheses. */
  public ProofState addHypothesis(Hypothesis hypothesis) {
    int last = _lastUsedIndex;
    if (hypothesis.getIndex() > last) last = hypothesis.getIndex();
    return new ProofState(_equations, _hypotheses.append(List.of(hypothesis)), _ordering,
                          _incomplete, last);
  }

  /**
   * Creates a copy of the current proof state with {@code ordreq} added to the ordering
   * requirements.
   */
  public ProofState addOrderingRequirement(OrdReq ordreq) {
    return new ProofState(_equations, _hypotheses, _ordering.append(List.of(ordreq)),
                          _incomplete, _lastUsedIndex);
  }

  /**
   * This returns a copy of the current proof state where the given equation context is marked as
   * incomplete.
   */
  public ProofState setIncomplete(int equationIndex) {
    if (_incomplete.contains(equationIndex)) return this;
    return new ProofState(_equations, _hypotheses, _ordering,
                          _incomplete.add(equationIndex), _lastUsedIndex);
  }

  /**
   * Returns whether this state is a final state, that is, the set of equation contexts, i.e.,
   * the proof goal, is empty.  This is also the case for the contradiction proof state!
   */
  public boolean isFinalState() {
    return _equations.isEmpty();
  }

  /**
   * Returns whether this is the unique "CONTRADICTION" proof state to indicate that we have
   * derived a contradiction.  The CONTRADICTION proof state is a final state.
   */
  public boolean isContradictionState() {
    return _contradiction;
  }

  /** Only for debugging / testing purposes! */
  public String toString() {
    if (_contradiction) return "CONTRADICTION";

    StringBuilder builder = new StringBuilder();
    builder.append("Equations:\n");
    for (EquationContext eq : _equations) {
      if (_incomplete.contains(eq.getIndex())) {
        builder.append(" " + eq.toString() + "  -- INCOMPLETE\n");
      }
      else builder.append(" " + eq.toString() + "\n");
    }
    if (!_hypotheses.isEmpty()) builder.append("Induction hypotheses:\n");
    for (Hypothesis hy : _hypotheses) builder.append(" " + hy.toString() + "\n");
    if (!_ordering.isEmpty()) builder.append("Ordering requirements:\n");
    for (OrdReq req : _ordering) builder.append(" * " + req.toString() + "\n");
    return builder.toString();
  }
}

