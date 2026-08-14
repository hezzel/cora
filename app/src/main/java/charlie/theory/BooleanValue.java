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

package charlie.theory;

import java.util.Map;
import charlie.types.Base;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.FunctionSymbolInherit;

/** BooleanValues are the function symbols true and false (which are both theory symbols). */
public final class BooleanValue extends FunctionSymbolInherit implements Value {
  private final boolean _value;

  BooleanValue(boolean b) {
    super(b ? "true" : "false", TypeFactory.boolSort, Value.SPECIALNAME);
    _value = b;
  }

  /** Returns the boolean value corresponding to this Boolean Value */
  public boolean getBool() {
    return _value;
  }

  /** @return the boolean sort */
  @Override
  public final Base queryType() { return TypeFactory.boolSort; }

  @Override
  public int hashCode(Map mu) { return _value ? 19 : 11; }

  /** @return false, since nullary constants cannot be infix */
  @Override
  public boolean isInfixSymbol() { return false; }

  /** @return this, since a value is not polymorphic, so substituting has no effect */
  public final BooleanValue substituteType(Type.ISubstitution typeMapping) { return this; }
}

