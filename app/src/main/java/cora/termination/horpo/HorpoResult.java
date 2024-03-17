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

package cora.termination.horpo;

import java.util.TreeMap;
import cora.terms.*;
import cora.trs.*;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.termination.TerminationAnswer;

/**
 * A HorpoResult contains the information needed to show that all left-hand sides are bigger than
 * all right-hand sides in a given TRS, using Constrained Horpo.
 *
 * Alternatively, if no such proof could be found, it contains that information too.
 */
class HorpoResult implements ProofObject {
  private final TreeMap<String,Integer> _pred;
  private final TreeMap<String,Integer> _stat;
  private int _bound;
  private String _failReason;

  HorpoResult(String reason) {
    _pred = null;
    _stat = null;
    _failReason = reason;
  }

  HorpoResult(TreeMap<String,Integer> precedence, TreeMap<String,Integer> status, int bound) {
    _pred = new TreeMap<String,Integer>(precedence);
    _stat = new TreeMap<String,Integer>(status);
    _bound = bound;
    _failReason = null;
  }

  public TerminationAnswer queryAnswer() {
    if (_pred == null) return TerminationAnswer.MAYBE;
    else return TerminationAnswer.YES;
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

  public String integerOrdering() {
    String ret = "{(x,y) | ";
    if (_bound <= 0) ret += "x > " + _bound + " ∧ x > y }";
    else ret += "x < " + _bound + " ∧ x < y }";
    return ret;
  }

  public void justify(OutputModule o) {
    if (_pred == null) {
      if (_failReason != null) o.println(_failReason);
      return;
    }

    o.println("Constrained HORPO succeedings in orienting all rules, using the following settings:");
    o.println("* Precedence (all non-mentioned symbols have precedence -1 for theory symbols and " +
      "0 for other symbols):");
    o.startTable();
    for (String symbol : _pred.keySet()) {
      o.nextColumn(symbol);
      o.nextColumn(":");
      o.println(_pred.get(symbol).toString());
    }
    o.endTable();
    o.println("* Status (all non-mentioned symbols have status Lex):");
    o.startTable();
    for (String symbol : _stat.keySet()) {
      o.nextColumn(symbol);
      o.nextColumn(":");
      o.println((_stat.get(symbol) <= 1 ? "Lex" : "Mul_" + _stat.get(symbol)));
    }
    o.endTable();
    o.println("* Well-founded theory orderings:");
    String symbol = switch (o.queryStyle()) {
      case OutputModule.Style.Unicode -> "⊐";
      default -> "[>]";
    };
    o.startTable();
    o.nextColumn(symbol + "_{Bool}");
    o.nextColumn("=");
    o.println("{(true,false)}");
    o.nextColumn(symbol + "_{Int}");
    o.nextColumn("=");
    o.println(integerOrdering());
    o.endTable();
  }
}
