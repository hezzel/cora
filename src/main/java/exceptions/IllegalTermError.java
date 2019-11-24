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
 * An IllegalTermError is thrown when something tries to construct a term that violates the
 * restrictions on formation for such terms; for example by creating a term that contains the same
 * variable both free and bound.
 */
public class IllegalTermError extends Error {
  private String _problem;

  public IllegalTermError(String problem) {
    super("Illegal term creation: " + problem);
    _problem = problem;
  }

  public String queryProblem() {
    return _problem;
  }
}

