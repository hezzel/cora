package charlie.util;

import java.util.function.BiFunction;
import java.util.function.BinaryOperator;

/**
 * The <b>Unit</b> type is a type with a single instance {@code unit}.
 * This instance doesn't have any method or property.
 * This type is mostly useful to be returned by the functorial interfaces.
 */
public class Unit {

  /**
   * The unique instance of {@code Unit}.
   */
  public static Unit unit = new Unit();

  public static BinaryOperator<Unit> combine = (x, y) -> unit;

  // The constructor of this object is private.
  private Unit() { }

  @Override
  public String toString() {
    return ":unit:";
  }
}
