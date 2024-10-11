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
import java.util.TreeMap;
import java.util.Set;
import java.util.TreeSet;
import charlie.util.Pair;
import charlie.terms.FunctionSymbol;
import charlie.smt.Valuation;
import cora.io.OutputModule;
import cora.termination.reduction_pairs.*;

/**
 * A HorpoResult is a ReductionPairProofObject that, aside from the basics, contains the information
 * needed to explain how an OrderingProblem was oriented using Constrained Horpo.
 *
 * Alternatively, if no such proof could be found, it contains that information too.
 */
class HorpoResult extends ReductionPairProofObject {
  private final HorpoParameters _parameters;
  private final HorpoConstraintList _constraints;
  private final Valuation _valuation;
  private final String _failReason;
  private final boolean _stronglyMonotonic;

  /** Create a failed proof (which will return MAYBE) */
  HorpoResult(OrderingProblem problem, String reason) {
    super(problem);
    _parameters = null;
    _constraints = null;
    _valuation = null;
    _stronglyMonotonic = false;
    _failReason = reason;
  }

  /**
   * Initialise a successful proof, for the given problem, with the given indexes within the problem
   * being oriented strictly (and the rest weakly), and the given indexes of conditional
   * requirements being relevant.
   * The other arguments are the parameters and constraint list that were used to solve the problem.
   * These can be queried for information interesting to print.
   * The valuation indicates how the variables in the parameters and constraint list should be
   * evaluated.
   */
  HorpoResult(OrderingProblem problem, Set<Integer> strict, Set<Integer> conds, Valuation valuation,
              HorpoParameters param, HorpoConstraintList hclst) {
    super(problem, strict, conds, problem.queryArgumentFilter().getRegardedArguments(valuation));
    _parameters = param;
    _constraints = hclst;
    _valuation = valuation;
    _stronglyMonotonic = problem.queryArgumentFilter().everythingIsRegarded(valuation);
    _failReason = null;
  }

  /**
   * If f > g in the precedence, returns a positive number.
   * If f < g in the precedence, returns a negative number.
   * If f = g (or they are never compared), returns 0.
   */
  public int precedence(FunctionSymbol f, FunctionSymbol g) {
    int fi, gi;
    if (_valuation == null) return 0;
    int k = _parameters.getPrecedence(f).evaluate(_valuation) -
            _parameters.getPrecedence(g).evaluate(_valuation);
    return k;
  }

  public int permutation(FunctionSymbol f, int index) {
    if (_valuation == null) return 0;
    return _parameters.getPermutation(f, index).evaluate(_valuation);
  }

  /** Returns whether the ordering is inherently strict. */
  public boolean stronglyMonotonic() {
    return _stronglyMonotonic;
  }

  /** Prints a string representation of the current integer ordering to the output module. */
  private void printIntegerOrdering(OutputModule module) {
    module.print("{(x,y) | ");
    boolean down = _parameters.getDirectionIsDownVariable().evaluate(_valuation);
    int bound = _parameters.queryIntegerBound();
    if (down) module.print("x %{greater} -%a %{and} x %{greater} y }", bound);
    else module.print("x %{smaller} %a %{and} x %{smaller} y }", bound);
  }

  /** Returns the set of all function symbols in the requirements we oriented. */
  private TreeSet<FunctionSymbol> getSymbols() {
    TreeSet<FunctionSymbol> ret = new TreeSet<FunctionSymbol>();
    for (OrderingRequirement req : _reqs) {
      req.left().storeFunctionSymbols(ret);
      req.right().storeFunctionSymbols(ret);
    }
    return ret;
  }

  /**
   * This prints the precedence and permutation for all function symbols.
   * As a side effect, this also shows the filter.
   */
  private void printSymbolData(OutputModule o) {
    ArrayList<HorpoParameters.SymbolData> data = _parameters.getSymbolData(_valuation);
    o.println("* Precedence and permutation:");
    o.startTable();
    for (int index = 0; index < data.size(); index++) {
      HorpoParameters.SymbolData d = data.get(index);
      // precedence: we print them in order, and note equality or greater then
      if (index == 0) o.nextColumn();
      else if (d.prec() == data.get(index-1).prec()) o.nextColumn("=");
      else o.nextColumn(">");
      // symbol
      o.nextColumn("%a ", d.symbol().queryName());
      // multiset arguments
      o.print("{");
      for (int i : d.mappedToOne()) o.print(" %a", i);
      o.nextColumn(" }");
      // lexicographically compared arguments
      int skip = 0;
      for (int i = 2; i <= d.symbol().queryArity(); i++) {
        if (d.mappedToGreater().containsKey(i)) {
          for (int j = 0; j < skip; j++) o.nextColumn("_");
          o.nextColumn("%a", d.mappedToGreater().get(i));
        }
        else skip++;
      }   
      o.println();
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
    if (_stronglyMonotonic) {
      o.println("* Monotonicity requirements: this is a strongly monotonic reduction pair " +
        "(all arguments of function symbols were regarded).");
      return;
    }
    o.println("* Disregarded arguments:");
    o.startTable();
    for (FunctionSymbol f : getSymbols()) {
      boolean first = true;
      for (int i = 1; i <= f.queryArity(); i++) {
        if (!regards(f, i)) {
          if (first) { o.nextColumn("%a", f.queryName()); first = false; }
          o.print("%a ", i);
        }
      }
      if (!first) o.println();
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
    printFilterings(o);
    printSymbolData(o);
    printOrderings(o);
  }
}
