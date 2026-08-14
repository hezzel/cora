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

import java.math.BigInteger;
import java.util.Map;
import charlie.types.Base;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.FunctionSymbolInherit;

/**
 * IntegerValues are the function symbols 0, 1, 2, ..., -1, -2, ...
 * They are theory symbols, and specifically correspond to the elements of the mathematical set
 * Z of integer numbers.  Since Z is unbounded, the value is stored as an arbitrary-precision
 * BigInteger.
 */
public final class IntegerValue extends FunctionSymbolInherit implements Value {
  private final BigInteger _value;

  IntegerValue(BigInteger i) {
    super(i.toString(), TypeFactory.intSort, Value.SPECIALNAME);
    _value = i;
  }

  /** Convenience constructor for the common case of a small (Java long) value. */
  IntegerValue(long i) {
    this(BigInteger.valueOf(i));
  }

  /** Returns the integer value corresponding to this Integer Value */
  public BigInteger getInteger() {
    return _value;
  }

  /** @return the integer sort */
  @Override
  public final Base queryType() { return TypeFactory.intSort; }

  @Override
  public int hashCode(Map mu) { return _value.hashCode(); }

  /** @return false, since nullary constants cannot be infix */
  @Override
  public boolean isInfixSymbol() { return false; }

  /** @return this, since a value is not polymorphic, so substituting has no effect */
  public IntegerValue substituteType(Type.ISubstitution typeMapping) { return this; }

}

