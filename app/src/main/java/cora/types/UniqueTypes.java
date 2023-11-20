package cora.types;

/**
 * This class keeps track of a number of important types Cora uses for specific
 * purposes, like the pre-defined theory types.
 */
final class UniqueTypes {
  // This class should not be instantiated
  private UniqueTypes() {}

  /** Returns the sort used to represent the set of integers. */
  public static final Base intSort = new Base("Int");

  /** Returns the sort used to represent the set of booleans. */
   public static final Base boolSort = new Base("Bool");

  /** Returns the sort used to represent the set of strings. */
  public static final Base stringSort = new Base("String");

  /** 
   * Returns the unit sort.
   * This is not a theory sort, but used for instance as the one sort in unsorted first-order TRSs.
   */
  public static final Base unitSort = new Base("o");

  static boolean isTheoryType(Type ty) {
    return
      ty == UniqueTypes.intSort  ||
      ty == UniqueTypes.boolSort ||
      ty == TypeFactory.stringSort;
  }
}
