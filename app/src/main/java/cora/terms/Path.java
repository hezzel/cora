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

package cora.terms;

/**
 * A path is a position that is uniquely associated to a specific term, and keeps track of every
 * subterm on the way from the top of the term to the subterm it references.  Hence, looking up the
 * subterm associated to this position takes no extra time, and it is easy to investigate whether
 * its context satisfies certain requirements.
 * Note: like Position, all instances of Path must (and can be expected to) be immutable.
 * Also note: while positions are preserved under alpha-conversion, subterms at these positions are
 * not: (λx.x)|_0 != (λy.y)|_0.  Hence, when using a Path, note that any binder variables in the
 * "corresponding subterm" may end up differing from the original term if substitute() or
 * refreshBinders() is called on that.
 */

public interface Path extends Position {
  /**
   * This returns the term that the Position is in; if the position is empty this is exactly the
   * corresponding subterm, if it is a position of length 1 it is a term whose direct argument is
   * the corresponding subterm, and so on.
   *
   * To find the path from this term to the corresponding subterm, take this term, the associated
   * subterm of its tail, and so on, until you reach the empty position.
   */
  Term queryAssociatedTerm();

  /**
   * This returns the subterm inside the associated term that is associated to the position.
   * Note that for every non-empty path p, p.queryCorrespondingSubterm() is the same as
   * p.tail().queryCorrespondingSubterm().
   */
  Term queryCorrespondingSubterm();

  /** 
   * If the position is in a subterm of some argument t, this function returns the position of
   * the relevant subterm in t; otherwise it throws an
   * InappropriatePatternDataError.
   */
  Path queryTail();
}
