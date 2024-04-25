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

import java.util.ArrayList;
import java.util.TreeMap;
import java.util.Set;
import charlie.util.Pair;
import charlie.terms.FunctionSymbol;
import charlie.smt.Valuation;
import cora.io.OutputModule;

/**
 * A HorpoResult contains the information needed to show that an OrderingProblem was satisfied
 * using Constrained Horpo.  It also tells us which of the "Either" inequalities were oriented
 * strictly.
 *
 * Alternatively, if no such proof could be found, it contains that information too.
 */
class HorpoResult extends ReductionPairProofObject {
  private final HorpoParameters _parameters;
  private final HorpoConstraintList _constraints;
  private final Valuation _valuation;
  private String _failReason;

  /** Create a failed proof (which will return MAYBE) */
  HorpoResult(OrderingProblem problem, String reason) {
    super(problem);
    _parameters = null;
    _constraints = null;
    _valuation = null;
    _failReason = reason;
  }

  /**
   * Initialise a successful proof, for the given problem, with the given indexes within the problem
   * being oriented strictly (and the rest weakly).
   * The other arguments are the parameters and constraint list that were used to solve the problem.
   * These can be queried for information interesting to print.
   * The valuation indicates how the variables in the parameters and constraint list should be
   * evaluated.
   */
  HorpoResult(OrderingProblem problem, Set<Integer> strict, Valuation valuation,
              HorpoParameters param, HorpoConstraintList hclst) {
    super(problem, strict);
    _parameters = param;
    _constraints = hclst;
    _valuation = valuation;
    _failReason = null;
  }

  /**
   * If f > g in the precedence, returns a positive number.
   * If f < g in the precedence, returns a negative number.
   * If f = g (or they are never compared), returns 0.
   */
  public int precedence(FunctionSymbol f, FunctionSymbol g) {
    int fi, gi;
    return _parameters.getPrecedenceFor(f).evaluate(_valuation) -
           _parameters.getPrecedenceFor(g).evaluate(_valuation);
  }

  /** Returns the status (Lex or Mul_i for some i ≥ 2) of the given symbol */
  public String status(FunctionSymbol f) {
    int k = _parameters.getStatusFor(f).evaluate(_valuation);
    if (k <= 1) return "Lex";
    else return "Mul_" + k;
  }

  /** Prints a string representation of the current integer ordering to the output module. */
  private void printIntegerOrdering(OutputModule module) {
    module.print("{(x,y) | ");
    boolean down = _parameters.getDirectionIsDownVariable().evaluate(_valuation);
    int bound = _parameters.queryIntegerBound();
    if (down) module.print("x %{greater} -%a %{and} x %{greater} y }", bound);
    else module.print("x %{smaller} %a %{and} x %{smaller} y }", bound);
  }

  /**
   * This prints the precedence and status.  Note: this only works because the Horpo process
   * ensures that the precedence is known whenever the status is known.
   */
  private void printPrecedence(OutputModule o) {
    ArrayList<HorpoParameters.SymbolData> data = _parameters.getSymbolData(_valuation);
    if (data.size() == 0) {
      o.println("* Precedence and status: all symbols may be oriented with Lex, and have the " +
        "same precedence.");
      return;
    }
    o.println("* Precedence and status (for non-mentioned symbols the precedence is irrelevant " +
      "and the status is Lex):");
    o.startTable();
    o.print("%a ", data.get(0).symbol());
    for (int index = 1; index <= data.size(); index++) {
      if (index == data.size() ||
          data.get(index).prec() != data.get(index-1).prec() ||
          data.get(index).stat() != data.get(index-1).stat()) {
        o.nextColumn();
        o.print("(status: %a)", data.get(index-1).stat() == 1 ? "Lex" : "Mul_" +
          data.get(index-1).stat());
        o.nextColumn();
        // Lex and Mul symbols cannot be equal (even if they are sometimes accidentally mapped to
        // the same integer because they are never compared), but two Mul symbols with different
        // counts *can* be equated
        if (index < data.size()) {
          if (data.get(index).prec() != data.get(index-1).prec() ||
              data.get(index-1).stat() == 1)
          o.println("%{greater}");
        }
        else o.println("=");
      }
      else o.print("= ");
      if (index < data.size()) o.print("%a ", data.get(index).symbol());
    }
    o.endTable();
  }

  /** This prints the orderings used for the theory sorts. */
  private void printOrderings(OutputModule o) {
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

  /** This prints information about variable regardings. */
  private void printFilterings(OutputModule o) {
    ArrayList<Pair<String,Integer>> disregarded = _parameters.getDisregardedArguments(_valuation);
    if (disregarded.size() == 0) {
      o.println("* Monotonicity requirements: this is a strongly monotonic reduction pair " +
        "(all arguments of function symbols were regarded).");
      return;
    }
    o.println("* Filter:");
    o.startTable();
    for (int i = 0; i < disregarded.size(); ) {
      String name = disregarded.get(i).fst();
      o.nextColumn("%a", name);
      o.nextColumn("disregards argument(s)");
      for (; i < disregarded.size() && disregarded.get(i).fst().equals(name); i++) {
        o.print("%a ", disregarded.get(i).snd());
      }
      o.println();
    }
    o.endTable();
  }

  public void justify(OutputModule o) {
    if (_parameters == null) {
      if (_failReason != null) o.println(_failReason);
      return;
    }

    o.println("Constrained HORPO yields:");
    printOrderingProblem(o);
    o.println("We do this using the following settings:");
    printPrecedence(o);
    printOrderings(o);
    printFilterings(o);
  }
}
