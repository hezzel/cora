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

package cora.termination.reduction_pairs;

import java.util.TreeMap;
import charlie.terms.FunctionSymbol;
import charlie.smt.*;

/**
 * The parameters to Horpo are the precedence, the status, the integer ordering, and the
 * monotonicity requirements.
 * The HorpoParameters class keeps track of Smt variables to represent precedence, status,
 * direction of integer ordering and monotonicity requirements.
 * It also maintains an SmtProblem to create variables in.
 */
class HorpoParameters {
  private final SmtProblem _problem;
  private final TreeMap<String,IVar> _precedence;
  private final TreeMap<String,IVar> _status;
  private final TreeMap<String,TreeMap<Integer,BVar>> _regards;
  private final BVar _down;
  private final int _M;
  private final BVar _alwaysTrue;
  private final boolean _strict;

  /**
   * Sets up a set of HorpoParameters with empty precedence and status: variables for these will be
   * created on the fly, as they are requested.
   * The given integer bound should be a positive number: it represents either the bound to count up
   * to, or the negation of the bound to count down to.
   * The given boolean indicates whether our parameters force a strongly monotonic ordering.
   */
  HorpoParameters(int bound, boolean strict) {
    _problem = new SmtProblem();
    _precedence = new TreeMap<String,IVar>();
    _status = new TreeMap<String,IVar>();
    _regards = new TreeMap<String,TreeMap<Integer,BVar>>();
    _strict = strict;
    _down = _problem.createBooleanVariable("down");
    _M = bound > 0 ? bound : 1;
    _alwaysTrue = _problem.createBooleanVariable("alwaystrue");
    _problem.require(_alwaysTrue);
  }

  /**
   * The HorpoParameters keep track of an SmtProblem, which is used for creating the Smt variables
   * associated to precedence, status etcetera.  It also contains the corresponding constraints.
   * Other Horpo-related tools are certainly allowed to add their own constraints (and variables)
   * to this problem.
   */
  public SmtProblem queryProblem() {
    return _problem;
  }

  /**
   * The precedence is represented by mapping every function symbol to an integer: term symbols ≥
   * 0, theory symbols < 0.
   *
   * This function returns an integer variable associated to the given symbol f.  It may be created
   * first in the underlying SMT problem if we hadn't done so yet; but it will always give the
   * same variable for the same function symbol.
   */
  public IVar getPrecedenceFor(FunctionSymbol f) {
    String name = f.queryName();
    if (_precedence.containsKey(name)) return _precedence.get(name);
    IVar x = _problem.createIntegerVariable("pred(" + name + ")");
    // theory symbols have values < 0, non-theory symbols ≥ 0
    if (f.isTheorySymbol()) _problem.require(SmtFactory.createSmaller(x, SmtFactory.createValue(0)));
    else _problem.require(SmtFactory.createGeq(x, SmtFactory.createValue(0)));
    _precedence.put(name, x);
    return x;
  }

  /**
   * The status is represented by an integer: a number 1 for Lex status, and k ≥ 2 for Mul_k.
   *
   * This function either returns an integer variable associated to the given symbol, or null.
   * In case the arity is 0 or 1, null is returned, because status is entirely irrelevant in this
   * case (so we may as well default to Lex).
   * Otherwise, an integer variable is returned that ranges over 1..ar(f).  It may be creaed first
   * in the underlying SMT problem if we hadn't done so yet; but it will always give the same
   * variable for the same function symbol.
   */
  public IVar getStatusFor(FunctionSymbol f) {
    if (f.queryArity() <= 1) return null;
    String name = f.queryName();
    if (_status.containsKey(name)) return _status.get(name);
    IVar x = _problem.createIntegerVariable("stat(" + name + ")");
    _status.put(name, x);
    _problem.require(SmtFactory.createGeq(x, SmtFactory.createValue(1)));
    _problem.require(SmtFactory.createLeq(x, SmtFactory.createValue(f.queryArity())));
    return x;
  }

  /**
   * The monotonicity requirements are represented by one boolean for every (function symbol,
   * argument index) pair.  The boolean represents whether the function symbol regards the given
   * argument (so must be monotonic in it), or ignores it.
   *
   * This function returns a boolean variable that should evaluate to true if the function symbol
   * does regard the given index, and to false if it doesn't (in which case the argument is
   * essentially filtered away).
   *
   * Note that in the case that we are required to build a strongly monotonic ordering, the same
   * variable will be returned for all function symbols and indexes: a variable that is forced to
   * true (since in this case, every function symbol must regard all its arguments).
   */
  public BVar getRegardsVariableFor(FunctionSymbol f, int index) {
    if (_strict || f.isTheorySymbol()) return _alwaysTrue;

    String name = f.queryName();
    TreeMap<Integer,BVar> map = _regards.get(name);
    if (map == null) {
      map = new TreeMap<Integer,BVar>();
      _regards.put(name, map);
    }
    BVar ret = map.get(index);
    if (ret == null) {
      ret = _problem.createBooleanVariable("regards(" + name + "," + index + ")");
      map.put(index, ret);
    }
    return ret;
  }

  /**
   * Integer variables may either be oriented upwards, or downwards.  This function returns a
   * boolean variable asserting that they go downwards; its negation expressions that the
   * orientation is upwards instead.
   */
  public BVar getDirectionIsDownVariable() {
    return _down;
  }

  /**
   * To ensure well-foundedness of the integer relation, decreases are only considered a strict
   * decrease if the decreasing theory term is at least -<some bound>; increases are only considered
   * a strict increase if the increasing theory term is at most <some bound>.  This function returns
   * the bound that may be used.
   *
   * This is the value the HorpoParameters were initialised with.
   */
  public int queryIntegerBound() {
    return _M;
  }
}

