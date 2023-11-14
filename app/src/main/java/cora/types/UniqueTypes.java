package cora.types;

final class UniqueTypes {

  // This class should not be instantiated
  private UniqueTypes() {}

  /**  */
  public static final Base intSort = new Base("Int");

  /** */
   public static final Base boolSort = new Base("Bool");

  /** */
  public static final Base stringSort = new Base("String");

  /** unitSort  */
  public static final Base unitSort = new Base("o");

  public static boolean isTheoryType(Type ty) {
    return
      ty == UniqueTypes.intSort  ||
      ty == UniqueTypes.boolSort ||
      ty == TypeFactory.stringSort;
  }
}
