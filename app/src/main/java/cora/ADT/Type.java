package cora.ADT;

import java.util.List;

/**
 * Types have the form σ1 → ,,, → σk → τ, with all σi Types and τ a BASE type.
 * For inductive reasoning, we split Types in two kinds: the BASE types, and ARROW types σ → τ;
 * here, σ1 → ... → σk → τ should be read in a right-associative way.
 * <p><br />
 * <b>Note:</b> all instances of Type must (and can be expected to) be immutable.
 * </p>
 */
public sealed interface Type permits Base, Arrow, Product {

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

  /** For σ1 → ,,, → σk → τ, returns τ */
  Type queryOutputType();

  /** For σ1 → ,,, → σk → τ, returns max(order(σ1),,,order(σk))+1 */
  int queryTypeOrder();

  // Throws an InappropriatePatternDataError if called on anything but ARROWTYPE */
//  cora.types.Type queryArrowInputType();
  // Throws an InappropriatePatternDataError if called on anything but ARROWTYPE */
//  cora.types.Type queryArrowOutputType();
}