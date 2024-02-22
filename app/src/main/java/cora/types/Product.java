package cora.types;

import com.google.common.collect.ImmutableList;
import org.jetbrains.annotations.NotNull;

import cora.exceptions.IndexingError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.ProdTypeConstructionError;

public record Product(ImmutableList<Type> types) implements Type {
  public Product {
    if (types == null) throw new NullInitialisationError("Product", "product list");
    if (types.size() < 2) throw new ProdTypeConstructionError();
  }

  /** Returns true only if this object is an instance of {@link cora.types.Product}. */
  @Override
  public boolean isProductType() { return true; }

  /** 
   * Returns true if the only base types sorts occurring in this type are theory sorts --
   * that is, the sorts specifically created as theory sorts by the TypeFactory.
   */
  @Override
  public boolean isTheoryType() {
    return types.stream().allMatch(Type::isTheoryType);
  }

  /** @return true */
  @Override
  public boolean hasProducts() {
    return true;
  }

  @Override
  public @NotNull String toString(){
    StringBuilder builder = new StringBuilder();
    (new TypePrinter()).printType(this, builder);
    return builder.toString();
  }

  @Override
  public boolean equals(Type type) {
    switch (type) {
      case Product(ImmutableList<Type> componentTypes):
        if (this.types.size() != componentTypes.size()) return false;
        for (int i = 0; i < this.types.size(); i++) {
          if (!this.types.get(i).equals(componentTypes.get(i))) return false;
        }
        return true;
      default: return false;
    }
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

  @Override
  public int numberSubtypes() {
    return this.types.size();
  }

  @Override
  public Type subtype(int index) {
    if (index <= 0 || index > this.types.size()) {
      throw new IndexingError("Product", "subtype", index, 1, this.types.size());
    }
    return this.types.get(index-1);
  }
}
