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
 * An UnsupportedTheoryException is called when a constraint or integer expression passed to the
 * SMT module has an unexpected subterms, for which no direct SMT translation exists (yet).
 */
public class UnsupportedTheoryException extends RuntimeException {
  public UnsupportedTheoryException(String term, String explanation) {
    super("Failed to translate " + term + " to SMT: " + explanation + ".");
  }
}

