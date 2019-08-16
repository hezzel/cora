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

package cora.terms;

import java.util.ArrayList;
import cora.exceptions.NullInitialisationError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.FunctionSymbol;

/** UserDefinedSymbols are FunctionSymbols which are not predefined within Cora. */
public class UserDefinedSymbol implements FunctionSymbol {
  private String _name;
  private Type _type;

  /**
   * A user-defined symbol is always identified by the combination of its name and its type.
   * Throws an error if the name or type is null, or if name is the empty string.
   */
  public UserDefinedSymbol(String name, Type type) {
    _name = name;
    _type = type;
    if (name == null) throw new NullInitialisationError("UserDefinedSymbol", "name");
    if (name.equals("")) throw new Error("Function Symbol created with empty name.");
    if (type == null) throw new NullInitialisationError("UserDefinedSymbol", "type");
  }

  /** Returns the name of the current user-defined symbol. */
  public String queryName() {
    return _name;
  }

  /** Returns the type of the current user-defined symbol. */
  public Type queryType() {
    return _type;
  }

  /** Returns a string that describes the function symbol; the type is not indicated. */
  public String toString() {
    return _name;
  }

  /**
   * Returns a string that uniquely identifies the function symbol (by combining its name and
   * type).
   */
  public String toUniqueString() {
    return _name + "{" + _type.toString() + "}";
  }

  public boolean equals(FunctionSymbol symbol) {
    if (symbol == null) return false;
    if (!_name.equals(symbol.queryName())) return false;
    return _type.equals(symbol.queryType());
  }
}

