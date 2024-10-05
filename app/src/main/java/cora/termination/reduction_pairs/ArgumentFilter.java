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
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.BiFunction;

/**
 * An argument filtering is a function that indicates for every function symbol a set of arguments
 * that should be regarded.  If an argument is not regarded, then replacing it by any other Term
 * will not affect how the overall term behaves in the ordering.
 *
 * The argument filtering is in principle conditional on some SMT problem, so rather than returning
 * booleans, it returns boolean variables to specify its rules.
 */
public class ArgumentFilter {
  private SmtProblem _problem;
  private TreeMap<FunctionSymbol,TreeMap<Integer,BVar>> _variables;
  private BVar _truthVar;
    // if set to something other than null, nothing is allowed to be filtered, so we always return
    // this variable

  /**
   * Creates an argument filtering that will use the given SMT problem to create its "regards"
   * variables.  The problem will be stored in the ArgumentFiltering.
   */
  public ArgumentFilter(SmtProblem problem) {
    _problem = problem;
    _variables = new TreeMap<FunctionSymbol,TreeMap<Integer,BVar>>();
    _truthVar = null;
  }

  /**
   * This function forces the current argument filtering to be an empty filtering: every BVar
   * indicating whether an argument should be regarded is forced to true.
   */
  public void forceEmpty() {
    if (_truthVar != null) return;  // it's been forced to empty before
    for (Map.Entry<FunctionSymbol,TreeMap<Integer,BVar>> entry : _variables.entrySet()) {
      for (Map.Entry<Integer,BVar> e : entry.getValue().entrySet()) {
        _problem.require(e.getValue());
      }
    }
    _truthVar = _problem.createBooleanVariable("alwaystrue");
    _problem.require(_truthVar);
  }

  /** This creates an ArgumentFiltering where every argument to every function must be regarded. */
  public static ArgumentFilter createEmptyFilter(SmtProblem problem) {
    ArgumentFilter ret = new ArgumentFilter(problem);
    ret.forceEmpty();
    return ret;
  }

  /** 
   * This returns a BVar indicating that function symbol f regards its indexth argument.
  * Here, index really should be in {1...arity(f)}, but if not a variable will still be returned;
  * it is the responsibility of the caller to deal with this properly.
   * 
   * Note that if the argument filtering has been forced to be empty (through the forceEmpty
   * function), this will always return the same BVar, which has been forced to true.
   */
  public BVar regards(FunctionSymbol f, int index) {
    if (_truthVar != null) return _truthVar;
    if (!_variables.containsKey(f)) _variables.put(f, new TreeMap<Integer,BVar>());
    TreeMap<Integer,BVar> fmap = _variables.get(f);
    if (fmap.containsKey(index)) return fmap.get(index);
    BVar newvar = _problem.createBooleanVariable("regards{" + f.queryName() + "," + index + "}");
    fmap.put(index, newvar);
    return newvar;
  }

  /**
   * For the given valuation, returns a non-smt-dependent function to evaluate which arguments were
   * regarded.  Note that this can only return false for function symbols and arguments that we have
   * actually been asked about; everything else is assumed to be unfiltered.
   */
  public BiFunction<FunctionSymbol,Integer,Boolean> getRegardedArguments(Valuation valuation) {
    TreeMap<FunctionSymbol,TreeSet<Integer>> ret = new TreeMap<FunctionSymbol,TreeSet<Integer>>();
    for (FunctionSymbol f : _variables.keySet()) {
      TreeMap<Integer,BVar> map = _variables.get(f);
      TreeSet<Integer> tmp = null;
      for (Integer i : map.keySet()) {
        BVar x = map.get(i);
        if (valuation.queryAssignment(x)) continue;
        if (tmp == null) {
          tmp = new TreeSet<Integer>();
          ret.put(f, tmp);
        }
        tmp.add(i);
      }
    }
    return (f, i) -> ret.containsKey(f) ? !ret.get(f).contains(i) : true;
  }

  /** For the given valuation, checks if all regards variables are set to true. */
  public boolean everythingIsRegarded(Valuation valuation) {
    for (Map.Entry<FunctionSymbol,TreeMap<Integer,BVar>> entry : _variables.entrySet()) {
      for (Map.Entry<Integer,BVar> e : entry.getValue().entrySet()) {
        if (!valuation.queryAssignment(e.getValue())) return false;
      }
    }
    return true;
  }
}

