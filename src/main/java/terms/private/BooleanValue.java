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

package cora.terms;

import java.util.List;
import java.util.Map;
import java.util.Set;
import cora.exceptions.InappropriatePatternDataError;
import cora.types.TypeFactory;

/** BooleanValues are the function symbols true and false (which are both theory symbols). */
class BooleanValue extends ValueInherit {
  private boolean _value;

  BooleanValue(boolean b) {
    super(TypeFactory.boolSort);
    _value = b;
  }

  /** Returns the string representation of this boolean. */
  public String queryName() {
    if (_value) return "true";
    else return "false";
  }

  /** Add the boolean to the given string builder. */
  public void addToString(StringBuilder builder, Map<Replaceable,String> renaming,
                          Set<String> avoid) {
    builder.append(queryName());
  }

  /** Returns the standard string representation of the symbol. */
  public String toUniqueString() {
    return queryName();
  }

  public boolean equals(FunctionSymbol symbol) {
    if (symbol == null) return false;
    if (!symbol.isValue()) return false;
    if (!symbol.queryType().equals(TypeFactory.boolSort)) return false;
    return symbol.toValue().getBool() == _value;
  }

  public boolean getBool() {
    return _value;
  }

  public int getInt() {
    throw new InappropriatePatternDataError("BooleanValue", "getInt", "integer values");
  }
}

