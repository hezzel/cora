package cora.terms.position;

import cora.exceptions.IllegalArgumentError;
import cora.exceptions.NullInitialisationError;

public record MetaPos(int index, Position tail) implements Position {
  public MetaPos(int index, Position tail) {
    if (index <= 0) {
      throw new IllegalArgumentError("MetaPos", "constructor", "given index ≤ 0");
    }
    if (tail == null) {
      throw new NullInitialisationError("MetaPos", "tail");
    }
    this.index = index;
    this.tail = tail;
  }

  public String toString() {
    return "!" + index + "." + tail.toString();
  }

  public boolean equals(Position other) {
    switch (other) {
      case MetaPos(int id, Position tl): return index == id && tail.equals(tl);
      default: return false;
    }
  }

  public int queryHead() {
    return - index;
  }

  public Position queryTail() {
    return tail;
  }
}
