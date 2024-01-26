package cora.types;

import org.jetbrains.annotations.NotNull;

import cora.exceptions.NullInitialisationError;
import cora.exceptions.IndexingError;
import cora.utils.Pair;

public record Arrow(Type left, Type right) implements Type {

  public Arrow(Type left, Type right) {
    if (left == null || right == null) {
      throw new NullInitialisationError("Arrow", "type");
    }
    this.left = left;
    this.right = right;
  }

  @Override
  public boolean isArrowType() { return true; }

  @Override
  public @NotNull String toString() {
    String leftStr = this.left.toString();
    String rightStr = this.right.toString();

    StringBuilder outLeft = new StringBuilder();

    //Cases to where to put parenthesis on a type A => B.
    switch (new Pair<Type, Type>(this.left, this.right)){
      case Pair(Base(_), _) ->
        outLeft.append(leftStr);
      case Pair(Arrow(_, _), _), Pair(Product(_), _) ->
        outLeft.append("(").append(leftStr).append(")");
    }
    return outLeft.append(" → ").append(rightStr).toString();
  }

  /** Returns true if all sorts in the type are theory sorts. */
  @Override
  public boolean isTheoryType() { return this.left.isTheoryType() && this.right.isTheoryType(); }

  /**
   * Returns whether the given Type is equal to us.
   *
   * @param type
   */
  @Override
  public boolean equals(Type type) {
    return switch (type){
      case Arrow(Type l, Type r) ->
        this.left.equals(l) && this.right.equals(r);
      default -> false;
    };
  }

  /**
   * For σ1 → ,,, → σm → τ, returns m.
   */
  @Override
  public int queryArity() { return 1 + this.right.queryArity(); }

  /**
   * For σ1 → ,,, → σm → τ, returns τ
   */
  @Override
  public Type queryOutputType() { return this.right.queryOutputType(); }

  /** Returns the type order for the current type. */
  @Override
  public int queryTypeOrder() {
    return Math.max(
      1 + this.left.queryTypeOrder(),
      this.right.queryTypeOrder()
    );
  }

  @Override
  public int numberSubtypes() {
    return 2;
  }

  @Override
  public Type subtype(int index) {
    if (index == 1) return this.left;
    if (index == 2) return this.right;
    throw new IndexingError("Arrow", "subtype", index, 1, 2);
  }

  @Override @Deprecated
  public Type queryArrowInputType() { return this.left; }

  @Override @Deprecated
  public Type queryArrowOutputType() { return this.right; }

}
