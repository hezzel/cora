package cora.terms.position;

import cora.exceptions.NullInitialisationError;

public record LambdaPos(Position tail) implements Position {
  public LambdaPos(Position tail) {
    if (tail == null) {
      throw new NullInitialisationError("LambdaPos", "tail");
    }
    this.tail = tail;
  }

  public String toString() {
    return "0." + tail.toString();
  }

  public boolean equals(Position other) {
    switch (other) {
      case LambdaPos(Position tl): return tail.equals(tl);
      default: return false;
    }
  }

  public Position append(Position p) {
    return new LambdaPos(this.tail.append(p));
  }

  public int queryHead() {
    return 0;
  }

  public Position queryTail() {
    return tail;
  }
}
