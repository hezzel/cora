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
 * An IllegalTermError is thrown when something tries to construct a certain kind of term in a way
 * that violates the restrictions for that term (for example, an Abstraction whose binder is not a
 * binder-variale).
 */
public class IllegalTermError extends Error {
  private final String _problem;

  public IllegalTermError(String classname, String problem) {
    super("Illegal term creation for " + classname + ": " + problem);
    _problem = problem;
  }

  public String queryProblem() {
    return _problem;
  }
}
