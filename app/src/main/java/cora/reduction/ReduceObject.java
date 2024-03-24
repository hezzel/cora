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

package cora.reduction;

import charlie.terms.Term;

/**
 * Reduce objects are representatives of rules or rule schemes: objects that can be applied on a
 * term, reducing it to another term of the same type.
 *
 * All instances of Scheme must (and can be expected to) be immutable.
 */
interface ReduceObject {
  /** This returns whether the current rule scheme can be applied to t at the head of the term. */
  boolean applicable(Term t);

  /**
   * If the current rule can be applied to t at the head, this returns the result of a head-most
   * reduction; otherwise it returns null.
   */
  Term apply(Term t);

  /** Gives a string representation of the current rule scheme. */
  String toString();
}

