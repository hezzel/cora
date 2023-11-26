package cora.terms.position;

import cora.exceptions.IllegalArgumentError;
import cora.exceptions.NullInitialisationError;

public record ArgumentPos(int index, Position tail) implements Position {
  public ArgumentPos(int index, Position tail) {
    if (index <= 0) {
      throw new IllegalArgumentError("ArgumentPos", "constructor", "given index ≤ 0");
    }
    if (tail == null) {
      throw new NullInitialisationError("ArgumentPos", "tail");
    }
    this.index = index;
    this.tail = tail;
  }

  public String toString() {
    return "" + index + "." + tail.toString();
  }

  public boolean equals(Position other) {
    switch (other) {
      case ArgumentPos(int id, Position tl): return index == id && tail.equals(tl);
      default: return false;
    }
  }
}
