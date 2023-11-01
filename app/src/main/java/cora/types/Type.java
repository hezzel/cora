/**************************************************************************************************
 Copyright 2019, 2022 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.types;

import java.util.List;

/**
 * Types have the form σ1 → ,,, → σk → τ, with all σi Types and τ a BASE type.
 * For inductive reasoning, we split Types in two kinds: the BASE types, and ARROW types σ → τ;
 * here, σ1 → ... → σk → τ should be read in a right-associative way.
 *
 * Note: all instances of Type must (and can be expected to) be immutable.
 */
public sealed interface Type permits
  Base, Arrow, Product {

  /** Returns true for base types, false for arrow types. */
  default boolean isBaseType(){ return false; }

  /** Return false for base types, true for arrow types. */
  default boolean isArrowType(){ return false; }

  /** */
  default boolean isProdType(){ return false; }

  /** Returns true if the type is fully built from theory sorts.
   * A type is a theory type if it is physically equal to one of the types
   * created by the TypeFactory class.
   * */
  boolean isTheoryType();
  
  /** Returns a string representation of the current type. */
  String toString();

  /** Returns whether the given Type is equal to us. */
  boolean equals(Type type);

  /** For σ1 → ,,, → σk → τ, returns k */
  default int queryArity(){ return 0; }

  /** For σ1 → ,,, → σk → τ, adds {σ1,,,σk} to the end of answer. */
  @Deprecated
  default void appendInputTypes(List<Type> answer) {};

  /** For σ1 → ,,, → σk → τ, returns τ */
  @Deprecated
  default Base queryOutputSort() { return null; }

  /** For σ1 → ,,, → σk → τ, returns τ */
  Type queryOutputType();

  /** For σ1 → ,,, → σk → τ, returns max(order(σ1),,,order(σk))+1 */
  int queryTypeOrder();

  /** Throws an InappropriatePatternDataError if called on anything but ARROWTYPE */
  @Deprecated
  default Type queryArrowInputType() { return null; }

  /** Throws an InappropriatePatternDataError if called on anything but ARROWTYPE */
  @Deprecated
  default Type queryArrowOutputType(){ return null; }
}
