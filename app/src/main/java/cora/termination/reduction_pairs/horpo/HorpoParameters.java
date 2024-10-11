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
import java.util.TreeSet;
import java.util.Collections;
import charlie.util.Pair;
import charlie.terms.FunctionSymbol;
import charlie.smt.*;
import cora.termination.reduction_pairs.ArgumentFilter;

/**
 * The parameters to Horpo are the precedence, the argument permutation, and the integer ordering.
 * The HorpoParameters class keeps track of Smt variables to represent these concepts, and also
 * maintains the SmtProblem to create variables in.
 */
class HorpoParameters {
  private final SmtProblem _problem;
  private final TreeMap<FunctionSymbol,IVar> _precedence;
  private final TreeMap<FunctionSymbol,TreeMap<Integer,IVar>> _permutation;
  private final BVar _down;
  private final int _M;

  /**
   * This sets up a set of HorpoParameters by generating boolean and integer variables in the SMT
   * problem to represent the precedence and argument permutation.  We do not create any variable
   * for N_f, because we implicitly assume that N_f is the maximum arity of any function symbol,
   * and since the set is finite, such number always exists.
   */
  HorpoParameters(int bound, TreeSet<FunctionSymbol> allsymbols, ArgumentFilter regards,
                  SmtProblem problem) {
    _problem = problem;
    _precedence = new TreeMap<FunctionSymbol,IVar>();
    _permutation = new TreeMap<FunctionSymbol,TreeMap<Integer,IVar>>();
    _down = _problem.createBooleanVariable("down");
    _M = bound > 0 ? bound : 1;
    setupPrecedence(allsymbols);
    setupPermutation(allsymbols, regards);
  }

  /**
   * Helper function for the constructor: creates a precedence variable for each function symbol
   * that occurs in the given list.
   */
  private void setupPrecedence(TreeSet<FunctionSymbol> symbols) {
    IntegerExpression zero = SmtFactory.createValue(0);
    IntegerExpression max = SmtFactory.createValue(symbols.size());
    IVar valuevar = null;

    for (FunctionSymbol f : symbols) {
      // values are always mapped to 0
      if (f.isValue()) {
        if (valuevar == null) {
          valuevar = _problem.createIntegerVariable("zero");
          _problem.require(SmtFactory.createEqual(valuevar, zero));
        }
        _precedence.put(f, valuevar);
      }
      // other function symbols are mapped to a number between 1 and max
      else {
        IVar x = _problem.createIntegerVariable("pred(" + f.queryName() + ")");
        _problem.require(SmtFactory.createSmaller(zero, x));
        _problem.require(SmtFactory.createGeq(max, x));
        _precedence.put(f, x);
      }
    }
  }

  /**
   * For every function symbol f of arity m, we set up variables π{f}(i) for 1 ≤ i ≤ m, and
   * require that π{f}(i) = 0 if and only if argument i is regarded (otherwise it is a number
   * between 1 and m).  We additionally require that when i != j, either π{f}(i) != π{f}(j) or
   * both are 1.
   */
  private void setupPermutation(TreeSet<FunctionSymbol> symbols, ArgumentFilter filter) {
    IntegerExpression zero = SmtFactory.createValue(0);
    IntegerExpression one = SmtFactory.createValue(1);
    for (FunctionSymbol f : symbols) {
      int m = f.queryArity();
      if (m == 0) continue;
      IntegerExpression mexp = SmtFactory.createValue(m);
      TreeMap<Integer,IVar> map = new TreeMap<Integer,IVar>();
      _permutation.put(f, map);
      for (int i = 1; i <= m; i++) {
        IVar x = _problem.createIntegerVariable("pi{" + f.queryName() + "}(" + i + ")");
        BVar reg = filter.regards(f, i);
        _problem.requireImplication(reg.negate(), SmtFactory.createEqual(x, zero));
        if (m == 1) _problem.requireImplication(reg, SmtFactory.createEqual(x, one));
        else {
          _problem.requireImplication(reg, SmtFactory.createGreater(x, zero));
          _problem.require(SmtFactory.createGeq(mexp, x));
        }
        map.put(i, x);
        for (int j = 1; j < i; j++) {
          _problem.requireImplication(SmtFactory.createEqual(x, map.get(j)),
                                      SmtFactory.createEqual(x, one));
        }
      }
    }
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
   * The precedence is represented by mapping every function symbol to an integer variable.  The
   * function symbol must be one that was passed to the parameters during initialisation.
   */
  public IVar getPrecedence(FunctionSymbol f) {
    return _precedence.get(f);
  }

  /**
   * The permutation is represented by mapping every functionsymbol-position pair to an integer
   * variable.  The function symbol must be one that was passed to the parameters during
   * initialisation, and the position between 1 and its arity.
   */
  public IVar getPermutation(FunctionSymbol f, int pos) {
    return _permutation.get(f).get(pos);
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

  record SymbolData(FunctionSymbol symbol, int prec, TreeSet<Integer> mappedToOne,
                    TreeMap<Integer,Integer> mappedToGreater) {
    /** debug output */
    public String toString() {
      StringBuilder ret = new StringBuilder();
      ret.append(symbol.queryName());
      ret.append(" : [ {");
      for (int i : mappedToOne) ret.append(" " + i);
      ret.append(" }");
      for (int i = 2; i <= symbol.queryArity(); i++) {
        if (mappedToGreater.containsKey(i)) ret.append(" " + mappedToGreater.get(i));
        else ret.append(" _");
      }
      ret.append(" ] (" + prec + ")");
      return ret.toString();
    }
  }
  
  /**
   * For the given valuation, returns the precedence and status of all the function symbols where
   * the precedence was queried, ordered from large to small.
   */
  public ArrayList<SymbolData> getSymbolData(Valuation valuation) {
    ArrayList<SymbolData> info = new ArrayList<SymbolData>();
    for (FunctionSymbol symbol : _precedence.keySet()) {
      int p = valuation.queryAssignment(_precedence.get(symbol));
      TreeSet<Integer> one = new TreeSet<Integer>();
      TreeMap<Integer,Integer> other = new TreeMap<Integer,Integer>();
      for (int i = 1; i <= symbol.queryArity(); i++) {
        IVar x = _permutation.get(symbol).get(i);
        int value = valuation.queryAssignment(x);
        if (value == 1) one.add(i);
        else if (value > 1) other.put(value, i);
      }
      info.add(new SymbolData(symbol, p, one, other));
    }
    Collections.sort(info, new Comparator<SymbolData>() {
      public int compare(SymbolData inf1, SymbolData inf2) {
        if (inf1.prec != inf2.prec) return inf2.prec - inf1.prec;
        return inf1.symbol.compareTo(inf2.symbol);
      }
    });
    return info;
  }
}

