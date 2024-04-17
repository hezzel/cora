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
import java.util.Set;
import charlie.terms.FunctionSymbol;
import cora.io.OutputModule;

/**
 * A HorpoResult contains the information needed to show that an OrderingProblem was satisfied
 * using Constrained Horpo.  It also tells us which of the "Either" inequalities were oriented
 * strictly.
 *
 * Alternatively, if no such proof could be found, it contains that information too.
 */
class HorpoResult extends ReductionPairProofObject {
  private final TreeMap<String,Integer> _pred;
  private final TreeMap<String,Integer> _stat;
  private int _bound;
  private String _failReason;

  /** Create a failed proof (which will return MAYBE) */
  HorpoResult(OrderingProblem problem, String reason) {
    super(problem);
    _pred = null;
    _stat = null;
    _failReason = reason;
  }

  /**
   * Initialise a successful proof, for the given problem, with the given indexes within the problem
   * being oriented strictly (and the rest weakly).
   * The other arguments are the precedence (a value for each function symbol, such that f |> g if
   * precedence[f] > precedence[g]); the status (an integer for each function symbol, with 0 meaning
   * Lexicographical status and a higher value multiset_{status[f]}), and a bound for the integer
   * comparison.
   */
  HorpoResult(OrderingProblem problem, Set<Integer> strict,
              TreeMap<String,Integer> precedence, TreeMap<String,Integer> status, int bound) {
    super(problem, strict);
    _pred = new TreeMap<String,Integer>(precedence);
    _stat = new TreeMap<String,Integer>(status);
    _bound = bound;
    _failReason = null;
  }

  /**
   * If f > g in the precedence, returns a positive number.
   * If f < g in the precedence, returns a negative number.
   * If f = g (or they are never compared), returns 0.
   */
  public int precedence(FunctionSymbol f, FunctionSymbol g) {
    int fi, gi;
    if (_pred.containsKey(f.toString())) fi = _pred.get(f.toString());
    else if (f.isTheorySymbol()) fi = -1;
    else fi = 0;
    if (_pred.containsKey(g.toString())) gi = _pred.get(g.toString());
    else if (g.isTheorySymbol()) gi = -1;
    else gi = 0;
    return fi - gi;
  }

  /** Returns the status (Lex or Mul_i for some i ≥ 2) of the given symbol */
  public String status(FunctionSymbol f) {
    if (!_stat.containsKey(f.toString())) return "Lex";
    if (_stat.get(f.toString()) <= 1) return "Lex";
    return "Mul_" + _stat.get(f.toString());
  }

  /** Prints a string representation of the current integer ordering to the output module. */
  private void printIntegerOrdering(OutputModule module) {
    module.print("{(x,y) | ");
    if (_bound <= 0) module.print("x %{greater} %a %{and} x %{greater} y }", _bound);
    else module.print("x %{smaller} %a %{and} x %{smaller} y }", _bound);
  }

  public void justify(OutputModule o) {
    if (_pred == null) {
      if (_failReason != null) o.println(_failReason);
      return;
    }

    o.println("Constrained HORPO yields:");
    printOrderingProblem(o);
    o.println("We do this using the following settings:");
    o.println("* Precedence (all non-mentioned symbols have precedence -1 for theory symbols and " +
      "0 for other symbols):");
    o.startTable();
    for (String symbol : _pred.keySet()) {
      o.nextColumn("%a", symbol);
      o.nextColumn(":");
      o.println("%a", _pred.get(symbol));
    }
    o.endTable();
    o.println("* Status (all non-mentioned symbols have status Lex):");
    o.startTable();
    for (String symbol : _stat.keySet()) {
      o.nextColumn("%a", symbol);
      o.nextColumn(":");
      o.println((_stat.get(symbol) <= 1 ? "Lex" : "Mul_" + _stat.get(symbol)));
    }
    o.endTable();
    o.println("* Well-founded theory orderings:");
    o.startTable();
    o.nextColumn("%{sqsupset}_{Bool}");
    o.nextColumn("=");
    o.println("{(true,false)}");
    o.nextColumn("%{sqsupset}_{Int}");
    o.nextColumn("=");
    printIntegerOrdering(o);
    o.println();
    o.endTable();
  }
}
