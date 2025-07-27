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
import charlie.types.Type;
import charlie.terms.FunctionSymbol;

/**
 * An IllegalSymbolException is thrown when a symbol occurs in a TRS or a term that should not be
 * there for whatever reason (for example a higher-order symbol in a first-order TRS).
 */
public class IllegalSymbolException extends UserException {
  public IllegalSymbolException(FunctionSymbol symbol, String kind, String explanation) {
    super("Illegal occurrence of symbol ", symbol.queryName(), " with type ",
      symbol.queryType(), " in " + kind + ": ", explanation);
  }
}
