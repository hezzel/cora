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

import charlie.types.Base;
import charlie.terms.FunctionSymbol;

/**
 * Values are constants of a theory sort. They cannot be rewritten, but rather, serve as the
 * representations of the elements of the underlying sets.
 *
 * The interface serves as a container to collect the concrete forms of values supported by Charlie
 * (i.e., values of specific types like integers).
 */
public sealed interface Value extends FunctionSymbol
    permits BooleanValue, IntegerValue, StringValue {

  /** Used as querySpecial() in value function symbols. */
  public static final String SPECIALNAME = "value";

  /** All Values have base type; to be precise, this will return a theory sort. */
  public abstract Base queryType();
}

