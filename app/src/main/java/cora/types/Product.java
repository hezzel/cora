package cora.types;

import com.google.common.collect.ImmutableList;
import cora.exceptions.ProdTypeConstructionError;
import org.jetbrains.annotations.NotNull;

public record Product(ImmutableList<Type> types) implements Type {
  public Product {
    if (types.size() < 2) throw new ProdTypeConstructionError();
  }

  /**
   *
   */
  @Override
  public boolean isProdType() { return true; }

  /**
   * Returns true if the type is fully built from theory sorts.
   * A type is a theory type if it is physically equal to one of the types
   * created by the TypeFactory class.
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
    for(int i = 0; i < types.size(); i++){
      if (i == 0) string.append(types.get(i).toString());
      String stringOfi = switch (types.get(i)){
        case Base(_)                 -> types.get(i).toString();
        case Arrow(_, _), Product(_) -> "(" + types.get(i).toString() + ")";
      };
      string.append(" x ").append(stringOfi);
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
        if(this.types.size() == componentTypes.size()){
          boolean isEqual = true;
          for(int i = 0; i < this.types.size(); i++){
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

  /**
   * For σ1 → ,,, → σk → τ, returns τ
   */
  @Override
  public Type queryOutputType() {
    return this;
  }

  /**
   * For σ1 → ,,, → σk → τ, returns max(order(σ1),,,order(σk))+1
   */
  @Override
  public int queryTypeOrder() {
    return types
      .stream()
      .map(Type::queryTypeOrder)
      .reduce(0, (n,m) -> Math.max(n,m));
  }
}
