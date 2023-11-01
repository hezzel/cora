package cora.ADT;

final public class TypeFactory {

  private TypeFactory() {}

  // Factory is here for compatibility
  /**  */
  public static Base intSort = UniqueTypes.intSort;

  /** */
  public static Base boolSort = UniqueTypes.boolSort;

  public static Base stringSort = UniqueTypes.stringSort;

}
