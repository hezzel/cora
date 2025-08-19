/**************************************************************************************************
 Copyright 2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.terms.replaceable;

import java.util.Set;

/**
 * Renamings are one-to-one mappings between Replaceables and Strings, giving each Replaceable a
 * unique name.  These are useful both in printing (ensuring that the same replaceable is printed
 * consistently with the same name) and in parsing (ensuring that a string refers 
 */
public interface Renaming {
  /** Returns the replaceables this Renaming gives a name to. */
  Set<Replaceable> domain();

  /** Returns the names used in this Renaming. */
  public Set<String> range();

  /** Returns the chosen name for the given replaceable, or null if it's not in the domain. */
  String getName(Replaceable x);

  /** Returns the replaceable with the given name, if there is one; null if not. */
  Replaceable getReplaceable(String name);

  /**
   * Makes a mutable copy of the current renaming.  Altering the copy will not affect the current
   * renaming.
   */
  MutableRenaming copy();

  /**
   * Puts an immutable wrapper around the present Renaming.  Beware: changing the present renaming
   * can still cause mutations to the result; only the objects that receive the immutable wrapper
   * cannot cause alterations to either it or the underlying Renaming.
   */
  Renaming makeImmutable();
}

