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

/**
 * A position indicates a location in a term, which has one of the following shapes:
 * - ε, which refers to the current term
 * - [index] tail, where the term is h(s1,...,sn), index ∈ {1..n}, and tail a position in s_index
 * - [0] tail, where the term is λx.s and tail a position in s
 * So this does NOT include head positions.
 *
 * A Position can be used to find (and possibly replace) the subterm at that position.
 * Note: all instances of Position must (and can be expected to) be immutable.
 */

public interface Position {
  /** Returns whether or not this is the empty position. */
  public boolean isEmpty();

  /** Returns whether or not this is an argument position. */
  public boolean isArgument();

  /** Returns whether or not this is a lambda position. */
  public boolean isLambda();

  /**
   * If the position is in a subterm of argument si of an application h(s1,...,sn), this function
   * returns the index i of the relevant argument (1..n); otherwise it throws an
   * InappropriatePatternDataError.
   */
  public int queryArgumentPosition();

  /**
   * If the position is in a subterm of some argument t, this function returns the position of
   * the relevant subterm in t; otherwise it throws an
   * InappropriatePatternDataError.
   */
  public Position queryTail();

  /** Returns whether this position and other represent the same location in a term. */
  public boolean equals(Position other);

  /** Represents the Position as a sequence of integers. */
  public String toString();
}

