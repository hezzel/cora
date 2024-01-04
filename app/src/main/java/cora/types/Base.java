package cora.types;

import org.jetbrains.annotations.NotNull;

import cora.exceptions.IndexingError;
import cora.exceptions.NullInitialisationError;

public record Base(String name) implements Type {
  public Base {
    if (name == null) {
      throw new NullInitialisationError("Base", "name");
    }
  }

  /**
   * Returns true only if this object is an instance of {@link cora.types.Base}.
   */
  @Override
  public boolean isBaseType() {
    return true;
  }

  /**
   * Returns true if the type is one of the internally-registered theory sorts.
   */
  @Override
  public boolean isTheoryType() {
    return UniqueTypes.isTheoryType(this);
  }

  @Override
  public @NotNull String toString() {
    return this.name;
  }

  @Override
  public int numberSubtypes() {
    return 0;
  }

  @Override
  public Type subtype(int index) {
    throw new IndexingError("Base", "subtype", index);
  }

  /**
   * Returns whether the given Type is equal to us.
   *
   * @param type
   */
  @Override
  public boolean equals(Type type) {
    return switch (type) {
      case Base(String x) -> this.name.equals(x);
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
    return 0;
  }
}
