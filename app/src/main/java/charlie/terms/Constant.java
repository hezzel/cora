/**************************************************************************************************
 Copyright 2019--2026 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.terms;

import java.util.Map;
import charlie.util.NullStorageException;
import charlie.types.Type;
import charlie.types.TVar;
import charlie.types.TVarSet;
import charlie.terms.replaceable.ReplaceableSet;

/**
 * Constants are the default kind of FunctionSymbol, typically used for user-defined function
 * symbols rather than in-built symbols or symbols specifically created for analysis.
 *
 * They are called Constants because they can also be seen as constant terms.
 */
class Constant extends FunctionSymbolInherit implements FunctionSymbol {
  /**
   * A constant is always identified by the combination of its name and its type.
   * Throws an error if the name or type is null, or if name is the empty string.
   */
  Constant(String name, Type type) {
    super(name, type, "");
    if (name == null) throw new NullStorageException("Constant", "name");
    if (name.equals("")) throw new IllegalArgumentException("Constant::constructor -- " +
      "Function Symbol created with empty name.");
  }

  /** @return false, since at this time there is no need for user-defined symbols to be infix. */
  public boolean isInfixSymbol() {
    return false;
  }

  /** @return a new constant, with the current constant's type substituted */
  public FunctionSymbol substituteType(Type.ISubstitution typeMapping) {
    return new Constant(queryName(), queryType().substitute(typeMapping));
  }
}
