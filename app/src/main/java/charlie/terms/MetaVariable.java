/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.terms;

import charlie.types.Type;

/**
 * Meta-variables are used in matching.  They take zero or more arguments to create a
 * meta-application.
 *
 * Multiple distinct meta-variables are allowed to share the same name.  In practice, we expect
 * multiple meta-variables within the same term or rule to have distinct names, but this is not
 * required.  Like variables, meta-variables may be renamed in pretty printing.  Hence,
 * meta-variable equality is not defined by their name, but rather by an internally kept index.
 *
 * Note: all instances of MetaVariable must (and can be expected to) be immutable.
 */
public interface MetaVariable extends Replaceable {
  /**
   * @return a string representation of the metavariable.
   * Metavariable names are not unique, and metavariables are not identified by their name.
   */
  String queryName();

  /**
   * @return the number of arguments the current meta-variable takes.
   * This is guaranteed to be a non-negative integer.
   */
  int queryArity();

  /**
   * @return σ_i if the current meta-variable has a type [σ_1 x ... x σ_k] → τ
   * (and 1 ≤ i ≤ k = queryArity())
   */
  Type queryInputType(int i);

  /** @return τ if the current meta-variable has a type [σ_1 x ... x σ_k] → τ */
  Type queryOutputType();

  /** @return σ_1 → ... → σ_k → τ if the current meta-variable has a type [σ_1 x ... x σ_k] → τ */
  Type queryType();
}

