/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.interfaces.types;

import java.util.ArrayList;

/**
 * Types have the form σ1 → ,,, → σk → τ, with all σi Types and τ a BASE type; this interface
 * considers the latter.
 * For now, base types are atomic, and are uniquely identified by their name. This may well change
 * in the future, however, so please compare them only using the equality function.
 *
 * Note: all instances of Type must (and can be expected to) be immutable.
 */
public interface BaseType extends Type {
  /** Returns whether the given BaseType is equal to us. */
  public boolean equals(BaseType sort);
}

