/**************************************************************************************************
 Copyright 2019--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.trs;

import charlie.util.UserException;
import charlie.terms.Term;

/**
 * An IllegalRuleException is thrown when something tries to construct a certain kind of rule in a
 * way that violates the restrictions for that rule (for example, a PatternRule where the left-hand
 * side is not a pattern).
 */
public class IllegalRuleException extends UserException {
  public IllegalRuleException(Term left, Term right, Term constraint, Object ...problem) {
    super(makeArray(left, right, constraint, problem));
  }

  public IllegalRuleException(String message) {
    super(message);
  }

  private static Object[] makeArray(Term left, Term right, Term constraint, Object[] problem) {
    boolean printConstraint =
      constraint != null && (!constraint.isValue() || !constraint.toValue().getBool());
    Object[] parts = new Object[printConstraint ? 7 + problem.length : 5 + problem.length];
    parts[0] = "Illegal rule [";
    parts[1] = left;
    parts[2] = " -> ";
    parts[3] = right;
    int a = 4;
    if (printConstraint) {
      parts[4] = " | ";
      parts[5] = constraint;
      a = 6;
    }
    parts[a] = "]: ";
    for (Object p : problem ) {
      a++;
      parts[a] = p;
    }
    return parts;
  }
}
