/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rewriting;

import cora.terms.Term;

/**
 * Rule schemes are a way to represent a countably infinite set of rules.  Typical examples of
 * rule schemes are beta, eta, and calculation rules.
 *
 * Note: all instances of Scheme must (and can be expected to) be immutable.
 */
public interface Scheme {
  /** Returns whether this is the beta rule scheme (λx.s) t → s[x:=t]. */
  boolean isBeta();

  /** Returns whether this is the eta-shortening rule scheme λx.s x → s with x ∉ FV(s) */
  boolean isEta();

  /** Returns whether this is a calculation scheme f(v1,...,vn) → w, with v1, ..., vn, w values. */
  boolean isCalc();

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

