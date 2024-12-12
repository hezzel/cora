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

import java.util.List;

import charlie.exceptions.IndexingException;
import charlie.exceptions.NullStorageException;
import charlie.util.FixedList;
import charlie.trs.Rule;
import charlie.trs.TRS;

/**
 * The current state of the proof, consisting of the set of equations that should be proved, a set
 * of equations that may be used as induction hypotheses, and a number of ordering requirements,
 * stored as rules.
 *
 * @apiNote A ProofState is immutable.
 */
public class ProofState {
  private final FixedList<Equation> _equations;
  private final FixedList<Equation> _hypotheses;
  private final FixedList<Rule> _ordering;

  /**
   * Instantiates a new proof state object with the following data:
   * @param initialEquations the list of equations to be proved.
   */
  public ProofState(FixedList<Equation> initialEquations) {
    if (initialEquations == null) {
      throw new NullStorageException("ProofState", "initialEquations cannot be null");
    }

    _equations = initialEquations;
    _hypotheses = FixedList.of();
    _ordering = FixedList.of();
  }

  /** Sets up a full proof state. */
  public ProofState(FixedList<Equation> equations, FixedList<Equation> hypotheses,
                     FixedList<Rule> ordering) {
    if (equations == null || hypotheses == null || ordering == null) {
      throw new NullStorageException("ProofState", "one of the arguments in full constructor");
    }
    _equations = equations;
    _hypotheses = hypotheses;
    _ordering = ordering;
  }
 
  /** Returns the list of equations in this proof state. */
  public FixedList<Equation> getEquations() {
    return _equations;
  }
 
  /** Returns the list of hypotheses in this proof state. */
  public FixedList<Equation> getHypotheses() {
    return _hypotheses;
  }

  /**
   * Returns the equation that's currently at the top of the list.
   * @throws IndexingException if there are no equations anymore.
   */
  public Equation getTopEquation() {
    if (_equations.isEmpty()) throw new IndexingException("ProofState", "getTopEquation", 0);
    return _equations.get(_equations.size()-1);
  }
  
  /**
   * Given a proof state and an equation {@code equation}, this method returns a new proof state in
   * which {@code equation} is added to the set of equations.  Everything else is unaltered.
   * @param equation the new equation
   * @return the new proof state
   */
  public ProofState addEquation(Equation equation) {
    return new ProofState(_equations.append(List.of(equation)), _hypotheses, _ordering);
  }

  /**
   * Given a proof state with E = {e1,...,en,e{n+1}} and an equation e', this method returns a proof
   * state in which E is updated to {e1,...,en,e'}.  Everything else is unaltered.
   * @param equation the new equation
   * @return the new proof state
   * @throws IndexingException if there is the set of equations is empty.
   */
  public ProofState replaceTopEquation(Equation newEquation) {
    return replaceTopEquation(List.of(newEquation));
  }

  /**
   * Given a proof state with E = {e1,...,en,e{n+1}} and a list of equations e'_1,...,e'_m, this
   * method returns a proof state in which E is updated to {e1,...,en,e'_1,...,e'_m}.  Everything
   * else is unaltered.
   * @param equation the new equation
   * @return the new proof state
   * @throws IndexingException if the set of equations is empty (so there is no top proof state
   *  to replace
   */
  public ProofState replaceTopEquation(List<Equation> newEquations) {
    if (_equations.isEmpty()) throw new IndexingException("ProofState", "replaceTopEquation", 0);
    FixedList.Builder<Equation> lst =
      new FixedList.Builder<Equation>(_equations.size() + newEquations.size());
    for (int i = 0; i < _equations.size()-1; i++) lst.add(_equations.get(i));
    for (Equation e : newEquations) lst.add(e);
    return new ProofState(lst.build(), _hypotheses, _ordering);
  }

  /**
   * Given a proof state with E = {e1,...,en,e{n+1}}, this method returns a proof state in which E
   * updated to {e1,...,en}.  Everything else is unaltered.
   */
  public ProofState deleteTopEquation() {
    return replaceTopEquation(List.of());
  }

  /** Creates a copy of the current proof state with {@code hypothesis} added to the hypotheses. */
  public ProofState addHypothesis(Equation hypothesis) {
    return new ProofState(_equations, _hypotheses.append(List.of(hypothesis)), _ordering);
  }

  /**
   * Creates a copy of the current proof state with {@code ordreq} added to the ordering
   * requirements.
   */
  public ProofState addOrderingRequirement(Rule ordreq) {
    return new ProofState(_equations, _hypotheses, _ordering.append(List.of(ordreq)));
  }

  /**
   * Returns whether this state is a final state, that is, the set of equations, i.e.,
   * the proof goal, is empty.
   */
  public boolean isFinalState() {
    return _equations.isEmpty();
  }

  /** Only for debugging / testing purposes! */
  public String toString() {
    StringBuilder builder = new StringBuilder();
    builder.append("Equations:\n");
    for (Equation eq : _equations) builder.append(" * " + eq.toString() + "\n");
    if (!_hypotheses.isEmpty()) builder.append("Induction hypotheses:\n");
    for (Equation eq : _hypotheses) builder.append(" * " + eq.toString() + "\n");
    if (!_ordering.isEmpty()) builder.append("Ordering requirements: all rules and\n");
    for (Rule req : _ordering) builder.append(" * " + req.toString() + "\n");
    return builder.toString();
  }
}
