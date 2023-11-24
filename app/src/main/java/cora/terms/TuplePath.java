package cora.terms;

import org.jetbrains.annotations.NotNull;
import cora.exceptions.*;

/**
 * A tuple path is a position of the form i.pos where i indicates the index of the ith component
 * of a tuple and pos is a subposition in that component.
 */
public class TuplePath implements Path {
  private int _componentIndex;
  private Path _tail;
  private Term _tm;

  TuplePath(@NotNull Term tm,@NotNull int componentIndex, @NotNull Path tail) {
    _componentIndex = componentIndex;
    _tail = tail;
    _tm = tm;

    if (tail == null) throw new NullInitialisationError("TuplePath", "tail");
    if (tm == null) throw new NullInitialisationError("TuplePath", "tm");

    if (!tm.isTuple()) {
      throw new InappropriatePatternDataError(
        "TuplePath",
        "TuplePath",
        "Tuple paths must be created only for tuple terms.");
    }
    if (componentIndex <= 0 || componentIndex > tm.numberTupleArguments()) {
      throw new IndexingError("TuplePath", "constructor", componentIndex, 1,
        tm.numberTupleArguments());
    }
    if (tm.queryTupleArgument(componentIndex) != tail.queryAssociatedTerm()) {
      throw new IllegalArgumentError("TuplePath", "constructor",
        "subterm " + componentIndex + " of " + tm + " is " +
        tm.queryArgument(componentIndex) + ", while tail refers to " +
        tail.queryAssociatedTerm() + ".");
    }
  }

  /**
   * This returns the term that the Position is in; if the position is empty this is exactly the
   * corresponding subterm, if it is a position of length 1 it is a term whose direct argument is
   * the corresponding subterm, and so on.
   * <p>
   * To find the path from this term to the corresponding subterm, take this term, the associated
   * subterm of its tail, and so on, until you reach the empty position.
   */
  @Override
  public Term queryAssociatedTerm() {
    return _tm;
  }

  /**
   * This returns the subterm inside the associated term that is associated to the position.
   * Note that for every non-empty path p, p.queryCorrespondingSubterm() is the same as
   * p.tail().queryCorrespondingSubterm().
   */
  @Override
  public Term queryCorrespondingSubterm() {
    return _tail.queryCorrespondingSubterm();
  }

  /**
   * Returns whether this is the empty position.
   */
  @Override
  public boolean isTuple() { return true; }

  public boolean isMeta() { return false; }
  public boolean isArgument() { return false; }
  public boolean isLambda() { return false; }
  public boolean isEmpty() { return false; }

  /**
   * If the position is in a subterm of argument si of an application h(s1,...,sn), this function
   * returns the index i of the relevant argument (1..n); otherwise it throws an
   * InappropriatePatternDataError.
   */
  @Override
  public int queryArgumentPosition() {
    throw new InappropriatePatternDataError("TuplePath",
    "queryArgumentPosition", "this is a tuple path.");
  }

  @Override
  public int queryComponentPosition() {
    return _componentIndex;
  }

  /**
   * If the position is in a subterm of argument si of a meta-application Z⟨s1,...,sk⟩, this
   * function returns the index i of the relevant argument (1..k); otherwise it throws an
   * InappropriatePatternDataError.
   */
  @Override
  public int queryMetaPosition() {
    throw new InappropriatePatternDataError(
      "TuplePath",
      "queryMetaPosition",
      "tuple positions of the form i.pos");
  }

  /**
   * If the position is in a subterm of some argument t, this function returns the position of
   * the relevant subterm in t; otherwise it throws an
   * InappropriatePatternDataError.
   */
  @Override
  public Path queryTail() {
    return _tail;
  }

  /**
   * Returns whether this position and other represent the same location in a term.
   *
   * @param other
   */
  @Override
  public boolean equals(Position other) {
    return other.isTuple() &&
           other.queryArgumentPosition() == _componentIndex &&
           _tail.equals(other.queryTail());
  }

  @Override
  public String toString() { return _componentIndex + "." + _tail.toString(); }
}
