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

package cora.exceptions;

/**
 * An IllegalRuleError is thrown when something tries to construct a certain kind of rule in a way
 * that violates the restrictions for that rule (for example, a PatternRule where the left-hand
 * side is not a pattern).
 */
public class IllegalRuleError extends Error {
  private String _problem;

  public IllegalRuleError(String classname, String problem) {
    super("Illegal rule creation for " + classname + ": " + problem);
    _problem = problem;
  }

  public String queryProblem() {
    return _problem;
  }
}

