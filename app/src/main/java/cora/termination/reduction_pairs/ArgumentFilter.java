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

import charlie.util.Pair;
import charlie.terms.FunctionSymbol;
import charlie.smt.BVar;
import charlie.smt.SmtProblem;
import charlie.smt.Valuation;

import java.util.ArrayList;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.BiFunction;

/**
 * An instance of the Monotonicity class that represents an argument filtering: a function that
 * regards a specific set of arguments, as described by an SMT problem.
 */
public class ArgumentFilter implements Monotonicity {
  private SmtProblem _problem;
  private TreeMap<FunctionSymbol,TreeMap<Integer,BVar>> _variables;

  /**
   * Creates an argument filtering that will use the given SMT problem to create its "regards"
   * variables.  The problem will be stored in the ArgumentFiltering.
   */
  public ArgumentFilter(SmtProblem problem) {
    _problem = problem;
    _variables = new TreeMap<FunctionSymbol,TreeMap<Integer,BVar>>();
  }

  /** @return false */
  public boolean stronglyMonotonic() {
    return false;
  }

  /** This always returns the same BVar, which has been forced to evaluate to true. */
  public BVar regards(FunctionSymbol f, int index) {
    if (!_variables.containsKey(f)) _variables.put(f, new TreeMap<Integer,BVar>());
    TreeMap<Integer,BVar> fmap = _variables.get(f);
    if (fmap.containsKey(index)) return fmap.get(index);
    BVar newvar = _problem.createBooleanVariable("regards{" + f.queryName() + "," + index + "}");
    fmap.put(index, newvar);
    return newvar;
  }

  /**
   * For the given valuation, returns a non-smt-dependent function to evaluate which arguments were
   * regarded.  Note that this will only include function symbols and arguments that we have
   * actually been asked about.
   */
  public BiFunction<FunctionSymbol,Integer,Boolean> getRegardedArguments(Valuation valuation) {
    TreeMap<FunctionSymbol,TreeSet<Integer>> ret = new TreeMap<FunctionSymbol,TreeSet<Integer>>();
    for (FunctionSymbol f : _variables.keySet()) {
      TreeMap<Integer,BVar> map = _variables.get(f);
      TreeSet<Integer> tmp = null;
      for (Integer i : map.keySet()) {
        BVar x = map.get(i);
        if (!valuation.queryAssignment(x)) continue;
        if (tmp == null) {
          tmp = new TreeSet<Integer>();
          ret.put(f, tmp);
        }
        tmp.add(i);
      }
    }
    return (f, i) -> ret.containsKey(f) && ret.get(f).contains(i);
  }
}

