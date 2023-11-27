package cora.terms.position;

import cora.exceptions.InappropriatePatternDataError;

public record EmptyPos() implements Position {
  public EmptyPos() {}

  public String toString() {
    return "ε";
  }

  public boolean equals(Position other) {
    switch (other) {
      case EmptyPos(): return true;
      default: return false;
    }
  }
  
  public boolean isEmpty() {
    return true;
  }

  public int queryHead() {
    throw new InappropriatePatternDataError("EmptyPos", "queryHead", "non-empty positions");
  }

  public Position queryTail() {
    throw new InappropriatePatternDataError("EmptyPos", "queryTail", "non-empty positions");
  }
}
