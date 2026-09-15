/**************************************************************************************************
 Copyright 2019--2026 Cynthia Kop

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

import java.lang.Comparable;
import java.util.Set;
import java.util.TreeSet;

/**
 * <p>Type ::= Base(String) | Arrow(Type, Type) | Data(String, Type, ..., Type) | TVar(String).</p>
 *
 * <p>Here, there are two kinds of sorts:</p>
 * <ul>
 * <li>base types: represented by a single name</li>
 * <li>data types: represented by a constructor (a name) and a non-empty list of arguments</li>
 * </ul>
 *
 * <p>In first-order term rewriting, all types are Base.</p>
 *
 * <p>In simply-typed rewriting, all types are Base or Arrow.</p>
 *
 * <p>Typically, data types that take arguments are used in polymorphic settings that also consider
 * type variables.  However, this is not mandatory; data types can also be useful for instance to
 * represent product types.</p>
 *
 * <p>Writing Arrow as the right-associative operator →, we can write all types in a form
 * σ1 → ... → σm → τ, where all σi are Types and τ is a sort or type variable.  This is often
 * used for inductive reasoning.</p>
 *
 * <p>Note: all instances of Type are immutable.</p>
 */
public sealed interface Type extends Comparable<Type> permits
  Base, Arrow, Data, TVar {

  /** Returns true for base types, false for arrow types, data types and type variables. */
  default boolean isBaseType() { return false; }

  /** Returns true for arrow types, false for base types, data types and type variables. */
  default boolean isArrowType() { return false; }

  /** Returns true for data types, false for base types, arrow types and type variables. */
  default boolean isDataType() { return false; }

  /** Returns true for type variables, false for base types, arrow types and data types. */
  default boolean isVariableType() { return false; }

  /** Returns true for base types and data types, false for arrow types and type variables. */
  boolean isSort();

  /** Returns true if this type is built exclusively from base types and arrows. */
  boolean isSimple();

  /**
   * Returns true if this type is a sort that is built exclusively from base types and data type
   * constructors (so no arrows or type variables): a sort with type order 0.
   */
  boolean isZeroSort();

  /**
   * Returns true if this is a monomorphic type: a type without any use of type variables.
   * (In first-order and simply-typed term rewriting, this is always the case.)
   */
  boolean isMonomorphic();

  /** For σ1 → ,,, → σm → τ with τ not an arrow type, returns m. */
  default int queryArity() { return 0; }

  /**
   * Returns the number of immediate subtypes.
   * For a base type or type variable, this is 0.
   * For an arrow type, this is 2.
   * For a data type c(A_1,...,A_n), this is n.
   */
  int queryNumberSubtypes();

  /**
   * If i is between 1 and queryNumberSubtypes(), this returns the corresponding subtype (from left
   * to right) of the type.  Otherwise, an IndexOutOfBoundsException is thrown.
   */
  Type querySubtype(int i);

  /** For σ1 → ,,, → σm → τ with τ not an arrow type, returns τ */
  default Type queryOutputType() { return this; }

  /**
   * Returns the type order of the current type.
   * For base types, this is 0.
   * For data types c(σ1,...,σk) it is max(order(σ1),...,order(σm)).
   * For σ1 → ... → σm → τ, it is max(order(σ1)+1,...,order(σk)+1,order(τ)).
   * And for type variables, it is undefined: if any type variable occurs anywhere in the type,
   * Integer.MAX_VALUE is returned.
   */
  int queryTypeOrder();

  /**
   * <p>ONLY RELEVANT FOR POLYMORPHIC TYPES: this function stores the type variables that occur in
   * the present type, into the given set.</p>
   *
   * <p>Since the given set is meant to be updated, it should be a mutable set.</p>
   *
   * <p>Complexity: linear in the size of the type.</p>
   *
   * <p>(For non-polymorphic types, this just doesn't do anything, but it does still cost linear
   * time.)</p>
   */
  void storeTypeVariables(Set<TVar> storage);

  /**
   * <p>ONLY RELEVANT FOR POLYMORPHIC TYPES: this function returns the type variables that occur in
   * the present type.</p>
   *
   * <p>Complexity: linear in the size of the type.</p>
   *
   * <p>(For non-polymorphic types, this returns an empty set, but it does still cost linear
   * time.)</p>
   */
  default TreeSet<TVar> listTypeVariables() {
    TreeSet<TVar> set = new TreeSet<TVar>();
    storeTypeVariables(set);
    return set;
  }

  /** Instantiated by Substitution (used to avoid a two-way dependency between packages). */
  interface ISubstitution {
    /** Returns null for type variables not in the domain and a Type for variables in the domain. */
    Type get(TVar alpha);
  }

  /** Instantiated by MutableSubstitution (used to avoid a two-way dependency between packages). */
  interface MSubstitution extends ISubstitution {
    /**
     * If key is not in the domain, adds key:=v to the domain and returns true.
     * (It will never be called with a key that *is* in the domain.)
     */
    boolean extend(TVar key, Type v);
  }

  /**
   * <p>ONLY RELEVANT FOR POLYMORPHIC TYPES: this function returns the type that is obtained by
   * replacing each occurrence of a type variable alpha in this type, by substitution.get(alpha).
   * Type variables that do not occur in the domain of the substitution are left unaltered.</p>
   *
   * <p>(Since types are immutable, this does not affect the current type; it only computes and
   * returns the substituted type).</p>
   *
   * <p>The given substitution will not be updated, so it is fine for the argument to be
   * immutable.</p>
   *
   * <p>(For non-polymorphic types, this just returns a copy of the type.)</p>
   */
  Type substitute(ISubstitution substitution);

  /**
   * ONLY RELEVANT FOR POLYMORPHIC TYPES: this function tries to extend substitution so that
   * this.instantiate(substitution) equals instance.  If successful, true is returned, and
   * substitution is fully updated as needed.  If unsuccessful, false is returned, but it is
   * possible that the substitution is still changed.
   */
  boolean match(Type instance, MSubstitution substitution);

  /** Returns whether the given Type is equal to us. */
  boolean equals(Type type);
}
