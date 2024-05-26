/**************************************************************************************************
 Copyright 2019--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.types;

import java.util.List;

/**
 * Type ::= Base | Arrow(Type, Type) | Product(Type,...,Type).
 *
 * Writing Arrow as the right-associative operator →, we can write all types in a form
 * σ1 → ... → σm → τ, with all σi are Types and τ is either a product type or a base
 * type.  This will often be used for inductive reasoning.
 *
 * Note: all instances of Type must (and can be expected to) be immutable.
 */
public sealed interface Type permits
  Base, Arrow, Product {

  /** Returns true for base types, false for arrow types and product types. */
  default boolean isBaseType() { return false; }

  /** Returns true for arrow types, false for base types and product types. */
  default boolean isArrowType() { return false; }

  /** Returns true for product types, false for base types and arrow types. */
  default boolean isProductType() { return false; }

  /**
   * Returns true if the only base types sorts occurring in this type are theory sorts --
   * that is, the sorts specifically created as theory sorts, accessible from the type
   * factory.
   */
  boolean isTheoryType();

  /** Returns true if and only if the type has a product type as subtype. */
  boolean hasProducts();
  
  /** Returns whether the given Type is equal to us. */
  boolean equals(Type type);

  /** For σ1 → ,,, → σm → τ, returns m. */
  default int queryArity() { return 0; }

  /** For σ1 → ,,, → σm → τ, returns τ */
  Type queryOutputType();

  /**
   * Returns the type order of the current type.
   * For base types, this is 0.  For product types (σ1,...,σk) it is max(order(σ1),...,order(σm)).
   * And for σ1 → ... → σm → τ, it is max(order(σ1)+1,...,order(σk)+1,order(τ)).
   */
  int queryTypeOrder();

  /**
   * Returns the number of immediate subtypes.
   * For an arrow tpye, this is 2.  For a product tpye A_1 x ... x A_n, this is n.
   * For a base type, this is 0.
   */
  int numberSubtypes();

  /**
   * If i is between 1 and numberSubtypes(), this returns the corresponding subtype (from left to
   * right) of the type.  Otherwise, an IndexingException is thrown.
   */
  Type subtype(int i);
}
