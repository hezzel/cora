/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.smt;

import java.util.ArrayList;
import java.util.TreeSet;
import cora.exceptions.NullInitialisationError;

/**
 * An SmtProblem keeps track of a list of integer and boolean variables, as well as a list of
 * requirements.
 */
public class SmtProblem {
  private TreeSet<Integer> _bvars;
  private TreeSet<Integer> _ivars;
  private ArrayList<Constraint> _constraints;
  private int _lastBooleanIndex;
  private int _lastIntegerIndex;

  public SmtProblem() {
    _bvars = new TreeSet<Integer>();
    _ivars = new TreeSet<Integer>();
    _constraints = new ArrayList<Constraint>();
    _lastBooleanIndex = 0;
    _lastIntegerIndex = 0;
  }

  // TODO: remove
  public IVar createIntegerVariable(int index) {
    _ivars.add(index);
    if (index > _lastIntegerIndex) _lastIntegerIndex = index;
    return new IVar(index);
  }

  /** Creates an integer variable with an index that has not yet been used. */
  public IVar createIntegerVariable() {
    _lastIntegerIndex++;
    _ivars.add(_lastIntegerIndex);
    return new IVar(_lastIntegerIndex);
  }

  // TODO: remove
  public BVar createBooleanVariable(int index) {
    _bvars.add(index);
    if (index > _lastBooleanIndex) _lastBooleanIndex = index;
    return new BVar(index);
  }

  /** Creates a boolean variable with an index that has not yet been used. */
  public BVar createBooleanVariable() {
    _lastBooleanIndex++;
    _bvars.add(_lastBooleanIndex);
    return new BVar(_lastBooleanIndex);
  }

  /**
   * This requires that the constraint holds.  Note that all variables in the constraint must have
   * been created through the createIntegerVariable or createBooleanVariable functions, since
   * this guarantees that they are stored in the SmtProblem.
   */
  public void require(Constraint c) {
    _constraints.add(c);
  }

  /**
   * This requires that premise → conclusion holds.  Note that all variables in both premise and
   * conclusion must have been created through the createIntegerVariable or createBooleanVariable
   * functions, since this guarantees that they are stored in the SmtProblem.
   */
  public void requireImplication(Constraint premise, Constraint conclusion) {
    _constraints.add(new Disjunction(new Not(premise), conclusion));
  }

  /** This reomves all stored constraints, but not variables. */
  public void clear() {
    _constraints.clear();
  }

  /** Returns the number of integer variables in this problem. */
  public int numberIntegerVariables() {
    return _ivars.size();
  }

  /** Returns the number of boolean variables in this problem. */
  public int numberBooleanVariables() {
    return _bvars.size();
  }

  /**
   * This calls an SMT solver to verify validity of the requirements.
   * Note that true is returned if the conjunction of the constraints is valid, and false is
   * returned if either it is not valid, or we cannot determine if it is valid.
   */
  public boolean isValid() {
    Constraint c = _constraints.size() == 0 ? new Truth() :
                   _constraints.size() == 1 ? _constraints.get(0) :
                   new Conjunction(_constraints);
    return ExternalSmtSolver.checkValidity(_bvars, _ivars, c);
  }

  /**
   * This calls an SMT solver to find a satisfying assignment of the requirements.
   * Note that if the conjunction of the constraints can be confirmed to be satisfiable, a
   * Valuation representing a satisfying assignment is returned.  However, if this cannot be
   * confirmed -- whether because it is unsatisfiable, the problem is too hard, or we run
   * into I/O issues -- then null is returned.
   */
  public Valuation satisfy() {
    Constraint c = _constraints.size() == 0 ? new Truth() :
                   _constraints.size() == 1 ? _constraints.get(0) :
                   new Conjunction(_constraints);
    return ExternalSmtSolver.checkSatisfiability(_bvars, _ivars, c);
  }

  /** Returns a string representation of all constraints in the problem, for debugging purposes */
  public String toString() {
    StringBuilder ret = new StringBuilder();
    for (int i = 0; i < _constraints.size(); i++) {
      _constraints.get(i).addToSmtString(ret);
      ret.append("\n");
    }
    return ret.toString();
  }

  /** Returns a string representation of the first n, or last -n constraints, for debugging. */
  public String toString(int num) {
    StringBuilder ret = new StringBuilder();
    int start = 0, end = _constraints.size();
    if (num > 0) { if (_constraints.size() > num) end = num; }
    else { start = _constraints.size() + num; if (start < 0) start = 0; }
    for (int i = start; i < end; i++) {
      _constraints.get(i).addToSmtString(ret);
      ret.append("\n");
    }
    return ret.toString();
  }
}

