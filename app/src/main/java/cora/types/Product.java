package cora.types;

import com.google.common.collect.ImmutableList;
import org.jetbrains.annotations.NotNull;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.ProdTypeConstructionError;

public record Product(ImmutableList<Type> types) implements Type {
  public Product {
    if (types == null) throw new NullInitialisationError("Product", "product list");
    if (types.size() < 2) throw new ProdTypeConstructionError();
  }

  /**
   * Returns true only if this object is an instance of {@link cora.types.Product}.
   */
  @Override
  public boolean isProdType() { return true; }

  /** 
   * Returns true if the only base types sorts occurring in this type are theory sorts --
   * that is, the sorts specifically created as theory sorts by the TypeFactory.
   */
  @Override
  public boolean isTheoryType() {
    return types
      .stream()
      .map(Type::isTheoryType)
      .reduce(true, (x, y) -> x && y);
  }

  @Override
  public @NotNull String toString(){
    StringBuilder string = new StringBuilder();
    for(int i = 0; i < types.size(); i++) {
      String stringOfi = switch (types.get(i)) {
        case Base(_) -> types.get(i).toString();
        case Arrow(_, _), Product(_) -> "(" + types.get(i).toString() + ")";
      };
      if (i == 0) string.append(stringOfi);
      else string.append(" x ").append(stringOfi);
    }
    return string.toString();
  }

  /**
   * Returns whether the given Type is equal to us.
   *
   * @param type
   */
  @Override
  public boolean equals(Type type) {
    return switch (type) {
      case Product(ImmutableList<Type> componentTypes) -> {
        if (this.types.size() == componentTypes.size()) {
          boolean isEqual = true;
          for (int i = 0; i < this.types.size(); i++) {
            isEqual = isEqual && this.types.get(i).equals(componentTypes.get(i));
          }
          yield isEqual;
        } else {
          yield  false;
        }
      }
      default -> false;
    };
  }

  /** For σ1 → ,,, → σm → τ, returns τ; so this returns itself. */
  @Override
  public Type queryOutputType() {
    return this;
  }

  /** Returns the type order of the current type. */
  @Override
  public int queryTypeOrder() {
    return types
      .stream()
      .map(Type::queryTypeOrder)
      .reduce(0, (n,m) -> Math.max(n,m));
  }
}
