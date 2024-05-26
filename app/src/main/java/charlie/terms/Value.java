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

import charlie.types.Base;

/**
 * Values are constants of a theory sorts that cannot be rewritten; they are the representations of
 * the elements of the underlying sets.
 */
public interface Value extends FunctionSymbol {
  /** All Values have base type; to be precise, this will return a theory sort. */
  public abstract Base queryType();

  /** @return whether this is an integer value (so its type is TypeFactory::intSort) */
  public boolean isIntegerValue();

  /** @return whether this is a boolean value (so its type is TypeFactory::boolSort) */
  public boolean isBooleanValue();

  /** @return whether this is a string value (so its type is TypeFactory::stringSort) */
  public boolean isStringValue();

  /**
   * For integer values, this returns the underlying integer; for other values, it causes an
   * InappropriatePatternDataException to be thrown.
   */
  public int getInt();

  /**
   * For boolean values, this returns the underlying boolean; for other values, it causes an
   * InappropriatePatternDataException to be thrown.
   */
  public boolean getBool();
}

