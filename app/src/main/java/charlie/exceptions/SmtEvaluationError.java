/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.exceptions;

/**
 * An SmtEvaluationError is called when something tries to evaluate a constraint or expression that
 * contains variables.
 */
public class SmtEvaluationError extends Error {
  public SmtEvaluationError(String varname) {
    super("Illegal attempt to evaluate constraint or expression with a variable " + varname + ".");
  }
}

