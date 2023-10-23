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

package cora.exceptions;

/**
 * A PatternRequiredError is thrown when a certain function may only be called on patterns, or on
 * semi-patterns (which may have subterms Z⟨x1,...,xk⟩(s1,...,sn) so long as all xi are distinct
 * binder variables), yet is called on something else.
 */
public class PatternRequiredError extends Error {
  public PatternRequiredError(String term, String function, String message) {
    super("Calling " + function + " on term " + term + " which is not supported: " + message);
  }
}

