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

package cora.termination.reduction_pairs.horpo;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.TreeMap;
import java.util.Collections;
import charlie.util.Pair;
import charlie.terms.FunctionSymbol;
import charlie.smt.*;

/**
 * The parameters to Horpo are the precedence, the argument permutation, the relevant arguments
 * count, and the integer ordering.
 * The HorpoParameters class keeps track of Smt variables to represent these concepts, and also
 * maintains the SmtProblem to create variables in.
 */
class HorpoParameters {
  private final SmtProblem _problem;
  private final TreeMap<String,IVar> _precedence;
  private final TreeMap<String,IVar> _status;
  private final BVar _down;
  private final int _M;

  /**
   * Sets up a set of HorpoParameters with empty precedence and argument comparison data: variables
   * for these will be created on the fly, as they are requested.
   * The given integer bound should be a positive number: it represents either the bound to count up
   * to, or the negation of the bound to count down to.
   */
  HorpoParameters(int bound, SmtProblem problem) {
    _problem = problem;
    _precedence = new TreeMap<String,IVar>();
    _status = new TreeMap<String,IVar>();
    _down = _problem.createBooleanVariable("down");
    _M = bound > 0 ? bound : 1;
  }

  /**
   * The HorpoParameters keep track of an SmtProblem, which is used for creating the Smt variables
   * associated to precedence, arguments permutation etcetera.  It also contains the corresponding
   * constraints.  Other Horpo-related tools are certainly allowed to add their own constraints
   * (and variables) to this problem.
   */
  SmtProblem queryProblem() {
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
  IVar getPrecedenceFor(FunctionSymbol f) {
    String name = f.queryName();
    if (_precedence.containsKey(name)) return _precedence.get(name);
    IVar x = _problem.createIntegerVariable("pred(" + name + ")");
    // theory symbols are always smaller than non-theory symbols
    if (f.isTheorySymbol()) _problem.require(SmtFactory.createSmaller(x, SmtFactory.createValue(0)));
    else _problem.require(SmtFactory.createGeq(x, SmtFactory.createValue(0)));
    _precedence.put(name, x);
    return x;
  }

  /**
   * The status is represented by an integer: a number 1 for Lex status, and k ≥ 2 for Mul_k.
   *
   * This function either returns an integer variable associated to the given symbol, or the value
   * 1.
   * In case the arity is 0 or 1, the value 1 is returned, because status is entirely irrelevant in
   * this case (so we may as well default to Lex).
   * Otherwise, an integer variable is returned that ranges over 1..ar(f).  It may be creaed first
   * in the underlying SMT problem if we hadn't done so yet; but it will always give the same
   * variable for the same function symbol.
   */
  public IntegerExpression getStatusFor(FunctionSymbol f) {
    if (f.queryArity() <= 1) return SmtFactory.createValue(1);
    String name = f.queryName();
    if (_status.containsKey(name)) return _status.get(name);
    IVar x = _problem.createIntegerVariable("stat(" + name + ")");
    _status.put(name, x);
    _problem.require(SmtFactory.createGeq(x, SmtFactory.createValue(1)));
    _problem.require(SmtFactory.createLeq(x, SmtFactory.createValue(f.queryArity())));
    // ensure that a precedence variable also exists, since these are returned together
    getPrecedenceFor(f);
    return x;
  }

  /**
   * Integer variables may either be oriented upwards, or downwards.  This function returns a
   * boolean variable asserting that they go downwards; its negation expressions that the
   * orientation is upwards instead.
   */
  BVar getDirectionIsDownVariable() {
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
  int queryIntegerBound() {
    return _M;
  }

  record SymbolData(String symbol, int prec, int stat) {}
  
  /**
   * For the given valuation, returns the precedence and status of all the function symbols where
   * the precedence was queried, ordered from large to small.
   */
  public ArrayList<SymbolData> getSymbolData(Valuation valuation) {
    ArrayList<SymbolData> info = new ArrayList<SymbolData>();
    for (String symbol : _precedence.keySet()) {
      int p = valuation.queryAssignment(_precedence.get(symbol));
      IVar i = _status.get(symbol);
      int s = (i == null) ? 1 : valuation.queryAssignment(i);
      info.add(new SymbolData(symbol, p, s));
    }
    Collections.sort(info, new Comparator<SymbolData>() {
      public int compare(SymbolData inf1, SymbolData inf2) {
        if (inf1.prec != inf2.prec) return inf2.prec - inf1.prec;
        if (inf1.stat != inf2.stat) return inf2.stat - inf1.stat;
        return inf1.symbol.compareTo(inf2.symbol);
      }
    });
    return info;
  }
}

