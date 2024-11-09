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

package charlie.terms;

import charlie.exceptions.InappropriatePatternDataException;
import charlie.types.TypeFactory;
import java.util.Map;

/** BooleanValues are the function symbols true and false (which are both theory symbols). */
class BooleanValue extends ValueInherit {
  private final boolean _value;

  BooleanValue(boolean b) {
    super(TypeFactory.boolSort);
    _value = b;
  }

  /** Returns the string representation of this boolean. */
  public String queryName() {
    if (_value) return "true";
    else return "false";
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

  public int hashCode(Map<Variable,Integer> mu) {
    return _value ? 19 : 11;
  }

  public boolean getBool() {
    return _value;
  }

  public String getString() {
    throw new InappropriatePatternDataException("BooleanValue", "getString", "string values");
  }

  public int getInt() {
    throw new InappropriatePatternDataException("BooleanValue", "getInt", "integer values");
  }
}
