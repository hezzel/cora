/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.interfaces.rewriting;

import java.util.ArrayList;
import cora.interfaces.types.Type;
import cora.interfaces.terms.Term;

/**
 * Rules are the core objects that define the reduction relation in a term rewriting system.
 * They have the form l -> r, where l and r have the same type.
 *
 * Note; all instances of Rule must (and can be expected to) be immutable.
 */
public interface Rule {
  /** For a rule l -> r, this function returns l. */
  Term queryLeftSide();

  /** For a rule l -> r, this function returns r. */
  Term queryRightSide();

  /** For a rule l -> r, returns the type of l (which should also be the type of r). */
  Type queryType();

  /** This returns whether the current rule can be applied to t at the top. */
  boolean applicable(Term t);

  /**
   * If the current rule can be applied to t at the top, this returns the result of a top-most
   * reduction; otherwise it returns null.
   */
  Term apply(Term t);

  /** Gives a string representation of the current rule. */
  String toString();
}

