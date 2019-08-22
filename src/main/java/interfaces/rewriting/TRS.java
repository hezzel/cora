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

import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Position;

/**
 * A TRS (term rewriting system) is an abstract rewriting system based on a set of rules.
 * It is key to rewriting, and it is that which we analyse for various properties.
 */
public interface TRS {
  /** @return the number of rules in the TRS that can be queried. */
  int queryRuleCount();

  /** For 0 <= index < queryRuleCount(), this returns one of the rules in the system. */
  Rule queryRule(int index);

  /**
   * Returns the FunctionSymbol associated to the given name in this TRS, if there is a unique
   * one.
   */
  FunctionSymbol lookupSymbol(String name);

  /**
   * Returns the leftmost, innermost position where a rule may be applied, or null if no such
   * position exists.
   */
  Position leftmostInnermostRedexPosition(Term s);

  /**
   * Reduces the given term at the leftmost, innermost redex position, and returns the result;
   * if no such position exists, null is returned instead.
   */
  Term leftmostInnermostReduce(Term s);
}

