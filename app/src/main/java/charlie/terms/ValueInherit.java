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
import charlie.types.*;
import charlie.terms.replaceable.ReplaceableSet;

/**
 * Values are constants of a theory sorts that cannot be rewritten; they are the representations of
 * the elements of the underlying sets.
 */
public abstract class ValueInherit extends FunctionSymbolInherit implements Value {
  protected ValueInherit(String name, Base mysort) {
    super(name, mysort, "value");
  }

  /** The type of a Value is always one of the theory sorts. */
  @Override
  public final Base queryType() { return (Base)super.queryType(); }

  /** @return false, since constants cannot be infix */
  public boolean isInfixSymbol() { return false; }

  /** @return true, since values are guaranteed to be theory symbols. */
  @Override
  public final boolean isTheorySymbol() { return true; }

  /** @return true, since values are theory terms */
  @Override
  public final boolean isTheoryTerm() { return true; }

  /** @return true */
  @Override
  public final boolean isValue() { return true; }

  /** @return this */
  @Override
  public final Value toValue() { return this; }

  /** @return null, since a value is not a calculation symbol */
  @Override
  public final CalculationSymbol toCalculationSymbol() { return null; }

  @Override
  public final boolean isIntegerValue() { return queryType().equals(TypeFactory.intSort); }

  @Override
  public final boolean isBooleanValue() { return queryType().equals(TypeFactory.boolSort); }

  @Override
  public final boolean isStringValue() { return queryType().equals(TypeFactory.stringSort); }

  /** @return this, since a value is not polymorphic, so substituting has no effect */
  public final FunctionSymbol substituteType(Type.ISubstitution typeMapping) { return this; }
}

