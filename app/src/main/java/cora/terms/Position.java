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

import cora.exceptions.InappropriatePatternDataError;

/**
 * A position indicates a location in a term, which has one of the following shapes:
 * <p><ul>
 *  <li> ε, which refers to the current term
 *  <li> [index] tail, where the term is h(s1,...,sn) or ⦅s1,..., sn⦆, index ∈ {1..n}, and tail a
 *  position in s_index
 *  <li> [0] tail, where the term is λx.s or (λx.s)(t1,...,tn)  and tail a position in s
 *  <li> ![index] tail, where the term is Z[s1,...,sk] or Z[s1,...,sk](t1,...,tn), index
 *  ∈ {1..k}, and tail a position in s_index.
 *  So this does NOT include head positions.
 *  </ul></p>
 * <p>
 * A Position can be used to find (and possibly replace) the subterm at that position.
 * <b>Note:</b> all instances of Position must (and can be expected to) be immutable.
 * </p>
 */

public interface Position {
  /** Returns whether this is the empty position. */
  boolean isEmpty();

  /** Returns whether this is an argument position. */
  boolean isArgument();

  /** Returns whether this is a tuple position. */
  boolean isTuple();

  /** Returns whether this is a lambda position. */
  boolean isLambda();

  /** Returns whether this is a meta position. */
  boolean isMeta();

  /**
   * If the position is in a subterm of argument si of an application h(s1,...,sn), this function
   * returns the index i of the relevant argument (1..n); otherwise it throws an
   * InappropriatePatternDataError.
   */
  int queryArgumentPosition();

  /**
   * If the position is in a subterm of component si of a tuple ⦅s1,..., sn⦆, this function
   * returns the index i of the relevant component (1..n); otherwise it throws an
   * InappropriatePatternDataError.
   */
  int queryComponentPosition();

  /**
   * If the position is in a subterm of argument si of a meta-application Z⟨s1,...,sk⟩, this
   * function returns the index i of the relevant argument (1..k); otherwise it throws an
   * InappropriatePatternDataError.
   */
  int queryMetaPosition();

  /**
   * If the position is in a subterm of some argument, component or meta-argument t, this
   * function returns the position of the relevant subterm in t; otherwise it throws an
   * InappropriatePatternDataError.
   */
  Position queryTail();

  /** Returns whether this position and other represent the same location in a term. */
  boolean equals(Position other);

  /** Represents the Position as a sequence of integers. */
  String toString();
}
