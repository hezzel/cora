/**************************************************************************************************
 Copyright 2019--2024 Cynthia Kop

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
 * An IllegalSymbolException is thrown when a symbol occurs in a TRS or a term that should not be
 * there for whatever reason (for example a higher-order symbol in a first-order TRS, or an
 * application symbol in a term that should be fully functional).
 */
public class IllegalSymbolException extends RuntimeException {
  private final String _problem;

  public IllegalSymbolException(String classname, String symbol, String problem) {
    super("Illegal symbol occurrence " + symbol + " in " + classname + ": " + problem);
    _problem = problem;
  }

  public String queryProblem() {
    return _problem;
  }
}
