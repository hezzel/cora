/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.terms;

import cora.types.Type;

/**
 * FunctionSymbols are the primary ingredient to construct terms.
 * Although function symbols may be overloaded and polymorphic in definition, we will consider
 * instances with different types as different symbols.
 *
 * Note: all instances of FunctionSymbol must (and can be expected to) be immutable.
 */
public interface FunctionSymbol extends Term {
  /**
   * All function symbols have a name that identifies how they are printed.
   * They are not necessarily identified uniquely by their name.
   */
  public String queryName();

  /** All function symbols have a type, which restricts how the symbol can be applied. */
  public Type queryType();

  /** Returns the number of arguments that this function symbol can (at most) be applied to. */
  public int queryArity();

  /** Returns true if this is a theory symbol (which has a meaning in some theory). */
  public boolean isTheorySymbol();

  /** Casts the symbol to a CalculationSymbol if it is one, otherwise returns null. */
  public CalculationSymbol toCalculationSymbol();

  /**
   * Returns a string that uniquely identifies the function symbol (which just the name does not).
   */
  public String toUniqueString();

  /**
   * Returns whether the current symbol is equal to another.
   * This is the case if they have the same name, typing and other properties (e.g., a value and a
   * non-value cannot be equal even if they have the same name and type).
   */
  public boolean equals(FunctionSymbol other);
}

