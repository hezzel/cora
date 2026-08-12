/**************************************************************************************************
 Copyright 2023--2026 Cynthia Kop

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
import charlie.types.TypeFactory;

/** BooleanValues are the function symbols true and false (which are both theory symbols). */
final class BooleanValue extends ValueInherit {
  private final boolean _value;

  BooleanValue(boolean b) {
    super(b ? "true" : "false", TypeFactory.boolSort);
    _value = b;
  }

  @Override
  public int hashCode(Map<Variable,Integer> mu) {
    return _value ? 19 : 11;
  }

  @Override
  public boolean getBool() {
    return _value;
  }

  @Override
  public String getString() {
    throw new InappropriatePatternDataException("BooleanValue", "getString", "string values");
  }

  @Override
  public java.math.BigInteger getInteger() {
    throw new InappropriatePatternDataException("BooleanValue", "getInteger", "integer values");
  }
}
