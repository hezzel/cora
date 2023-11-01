package cora.ADT;

final class UniqueTypes {

  // This class should not be instantiated
  private UniqueTypes() {}

  /**  */
  public static Base intSort = new Base("Int");

  /** */
   public static Base boolSort = new Base("Bool");

  /** */
  public static Base stringSort = new Base("String");

  public static boolean isTheoryType(Type ty) {
    return
      ty == UniqueTypes.intSort  ||
      ty == UniqueTypes.boolSort ||
      ty == TypeFactory.stringSort;
  }

}
