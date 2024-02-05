/**************************************************************************************************
 Copyright 2023 Cynthia Kop

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
 * requirements.  It also indirectly serves as a factory for making appropriate constraints.
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

  public static IntegerExpression createValue(int v) {
    return new IValue(v);
  }
  
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

  public static IntegerExpression createAddition(IntegerExpression arg1, IntegerExpression arg2) {
    if (arg1 == null) throw new NullInitialisationError("IPlus", "left argument");
    if (arg2 == null) throw new NullInitialisationError("IPlus", "right argument");
    return new Addition(arg1, arg2);
  }

  public static IntegerExpression createMultiplication(IntegerExpression arg1, IntegerExpression arg2) {
    if (arg1 == null) throw new NullInitialisationError("ITimes", "left argument");
    if (arg2 == null) throw new NullInitialisationError("ITimes", "right argument");
    return new Multiplication(arg1, arg2);
  }

  public static IntegerExpression createNegation(IntegerExpression arg) {
    if (arg == null) throw new NullInitialisationError("IMinus", "argument");
    return new Minus(arg);
  }

  public static IntegerExpression createDivision(IntegerExpression arg1, IntegerExpression arg2) {
    if (arg1 == null) throw new NullInitialisationError("IDiv", "left argument");
    if (arg2 == null) throw new NullInitialisationError("IDiv", "right argument");
    return new Division(arg1, arg2);
  }

  public static IntegerExpression createModulo(IntegerExpression arg1, IntegerExpression arg2) {
    if (arg1 == null) throw new NullInitialisationError("IMod", "left argument");
    if (arg2 == null) throw new NullInitialisationError("IMod", "right argument");
    return new Modulo(arg1, arg2);
  }

  public static Constraint createValue(boolean b) {
    if (b) return new Truth();
    else return new Falsehood();
  }

  public static Constraint createTrue() {
    return new Truth();
  }

  public static Constraint createFalse() {
    return new Falsehood();
  }

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

  public static Constraint createGreater(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullInitialisationError("BGreater", "left argument");
    if (right == null) throw new NullInitialisationError("BGreater", "right argument");
    return new Greater(left, right);
  }

  public static Constraint createSmaller(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullInitialisationError("BGreater", "reversed right argument");
    if (right == null) throw new NullInitialisationError("BGreater", "reversed left argument");
    return new Greater(right, left);
  }

  public static Constraint createGeq(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullInitialisationError("BGeq", "left argument");
    if (right == null) throw new NullInitialisationError("BGeq", "right argument");
    return new Geq(left, right);
  }

  public static Constraint createLeq(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullInitialisationError("BGeq", "reversed right argument");
    if (right == null) throw new NullInitialisationError("BGeq", "reversed left argument");
    return new Geq(right, left);
  }

  public static Constraint createEqual(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullInitialisationError("BEqual", "left argument");
    if (right == null) throw new NullInitialisationError("BEqual", "right argument");
    return new Equal(left, right);
  }

  public static Constraint createUnequal(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullInitialisationError("BDistinct", "left argument");
    if (right == null) throw new NullInitialisationError("BDistinct", "right argument");
    return new Distinct(left, right);
  }

  public static Constraint createNegation(Constraint c) {
    if (c == null) throw new NullInitialisationError("Not", "argument");
    return new Not(c);
  }

  public static Constraint createConjunction(Constraint a, Constraint b) {
    if (a == null) throw new NullInitialisationError("Conjunction", "left argument");
    if (b == null) throw new NullInitialisationError("Conjunction", "right argument");
    return new Conjunction(a, b);
  }

  public static Constraint createDisjunction(Constraint a, Constraint b) {
    if (a == null) throw new NullInitialisationError("Disjunction", "left argument");
    if (b == null) throw new NullInitialisationError("Disjunction", "right argument");
    return new Disjunction(a, b);
  }

  public static Constraint createDisjunction(ArrayList<Constraint> args) {
    if (args == null) throw new NullInitialisationError("Disjunction", "argument list");
    for (int i = 0; i < args.size(); i++) {
      if (args.get(i) == null) {
        throw new NullInitialisationError("Disjunction", "argument " + (i+1));
      }
    }
    if (args.size() == 0) return new Falsehood();
    if (args.size() == 1) return args.get(0);
    return new Disjunction(args);
  }

  public static Constraint createImplication(Constraint a, Constraint b) {
    if (a == null) throw new NullInitialisationError("Implication", "left argument");
    if (b == null) throw new NullInitialisationError("Implication", "right argument");
    return new Disjunction(new Not(a), b);
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

  /** This removes all stored constraints, but not variables. */
  public void clear() {
    _constraints.clear();
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
    return SmtSolver.checkValidity(_bvars, _ivars, c);
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
    return SmtSolver.checkSatisfiability(_bvars, _ivars, c);
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

