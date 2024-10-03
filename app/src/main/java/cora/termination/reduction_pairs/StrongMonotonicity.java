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

import charlie.terms.FunctionSymbol;
import charlie.smt.BVar;
import charlie.smt.Valuation;
import charlie.smt.SmtProblem;
import java.util.function.BiFunction;

/**
 * An instance of the Monotonicity class that requires strong monotonicity regardless of any
 * underlying SMT problem.
 */
public class StrongMonotonicity implements Monotonicity {
  private BVar _truthVar;

  /**
   * Creates a strong monotonicity problem that will use the given SMT problem to create its return
   * variables (these will always be forced to true).
   */
  public StrongMonotonicity(SmtProblem problem) {
    _truthVar = problem.createBooleanVariable("alwaystrue");
    problem.require(_truthVar);
  }

  /** @return true */
  public boolean stronglyMonotonic() {
    return true;
  }

  /** This always returns the same BVar, which has been forced to evaluate to true. */
  public BVar regards(FunctionSymbol f, int index) {
    return _truthVar;
  }

  /** This returns the function that always returns true. */
  public BiFunction<FunctionSymbol,Integer,Boolean> getRegardedArguments(Valuation valuation) {
    return (f, i) -> true;
  }
}

