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

import java.util.Map;
import charlie.exceptions.InappropriatePatternDataException;
import charlie.types.TypeFactory;

/**
 * IntegerValues are the function symbols 0, 1, 2, ..., -1, -2, ...
 * They are theory symbols, and specifically correspond to the elements of the mathematical set
 * Z of integer numbers.
 */
class IntegerValue extends ValueInherit {
  private final int _value;

  IntegerValue(int i) {
    super(TypeFactory.intSort);
    _value = i;
  }

  /** Returns the string representation of this integer. */
  public String queryName() {
    return "" + _value;
  }

  /** Returns the standard string representation of the symbol. */
  public String toUniqueString() {
    return "" + _value;
  }

  public boolean equals(FunctionSymbol symbol) {
    if (symbol == null) return false;
    if (!symbol.isValue()) return false;
    if (!symbol.queryType().equals(TypeFactory.intSort)) return false;
    return symbol.toValue().getInt() == _value;
  }

  public int hashCode(Map<Variable,Integer> mu) {
    return _value;
  }

  public int getInt() {
    return _value;
  }

  public String getString() {
    throw new InappropriatePatternDataException("IntegerValue", "getString", "string values");
  }

  public boolean getBool() {
    throw new InappropriatePatternDataException("IntegerValue", "getBool", "boolean values");
  }
}

