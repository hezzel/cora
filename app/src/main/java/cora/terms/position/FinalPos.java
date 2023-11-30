package cora.terms.position;

import cora.exceptions.IllegalArgumentError;
import cora.exceptions.InappropriatePatternDataError;

public record FinalPos(int chopcount) implements Position {
  public FinalPos(int chopcount) {
    if (chopcount < 0) throw new IllegalArgumentError("FinalPos", "constructor", "chop count < 0");
    this.chopcount = chopcount;
  }

  public String toString() {
    if (chopcount == 0) return "ε";
    else return "☆" + chopcount;
  }

  public boolean equals(Position other) {
    switch (other) {
      case FinalPos(int k): return chopcount == k;
      default: return false;
    }
  }
  
  public boolean isEmpty() {
    return chopcount == 0;
  }

  public boolean isFinal() {
    return true;
  }

  public int queryChopCount() {
    return chopcount;
  }

  public int queryHead() {
    throw new InappropriatePatternDataError("FinalPos", "queryHead", "non-empty positions");
  }

  public Position queryTail() {
    throw new InappropriatePatternDataError("FinalPos", "queryTail", "non-empty positions");
  }
}
