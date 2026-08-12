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

import java.math.BigInteger;
import java.util.Map;
import charlie.types.TypeFactory;

/**
 * IntegerValues are the function symbols 0, 1, 2, ..., -1, -2, ...
 * They are theory symbols, and specifically correspond to the elements of the mathematical set
 * Z of integer numbers.  Since Z is unbounded, the value is stored as an arbitrary-precision
 * BigInteger.
 */
final class IntegerValue extends ValueInherit {
  private final BigInteger _value;

  IntegerValue(BigInteger i) {
    super(i.toString(), TypeFactory.intSort);
    _value = i;
  }

  /** Convenience constructor for the common case of a small (Java long) value. */
  IntegerValue(long i) {
    this(BigInteger.valueOf(i));
  }

  @Override
  public int hashCode(Map<Variable,Integer> mu) {
    return _value.hashCode();
  }

  @Override
  public BigInteger getInteger() {
    return _value;
  }

  @Override
  public String getString() {
    throw new InappropriatePatternDataException("IntegerValue", "getString", "string values");
  }

  @Override
  public boolean getBool() {
    throw new InappropriatePatternDataException("IntegerValue", "getBool", "boolean values");
  }
}

