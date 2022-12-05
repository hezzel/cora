/**************************************************************************************************
 Copyright 2022 Cynthia Kop

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

public class RuleFactory {
  /**
   * Create a first-order rule.  If left or right is not first-order, this will cause an
   * IllegalRuleError to be thrown.
   */
  public static Rule createFORule(Term left, Term right) {
    return new FirstOrderRule(left, right);
  }

  /**
   * Create an applicative higher-order rule.
   */
  public static Rule createAtrsRule(Term left, Term right) {
    return new AtrsRule(left, right);
  }
}

