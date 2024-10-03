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

import java.util.function.BiFunction;

/**
 * A Monotonicity class represents the monotonicity requirements a reduction pair should satisfy.
 * This could either be a requirement to be fully monotonic, or to regard or disregard certain
 * parameters of function symbols.
 *
 * The Monotonicity class is often conditional on some SMT problem, so rather than returning
 * booleans, it returns boolean variables to specify its rules.
 */
public interface Monotonicity {
  /**
   * If the reduction pair should be strongly monotonic, without any dependencies on an SMT
   * problem, this returns true.  If not, it returns false.
   */
  public boolean stronglyMonotonic();

  /**
   * This returns a BVar indicating that function symbol f regards its indexth argument.
   * Here, index should be in {1...arity(f)}.  If this is not the case, anything may happen,
   * including a null return value or an Exception being thrown.
   */
  public BVar regards(FunctionSymbol f, int index);

  /**
   * For the given valuation, returns for each function symbol and integer whether it needs to be
   * regarded.  For function symbols / argument indexes that were never asked about, this errs on
   * the side of not regarding them, unless stronglyMonotonic() is true.
   */
  public BiFunction<FunctionSymbol,Integer,Boolean> getRegardedArguments(Valuation valuation);
}

