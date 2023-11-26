package cora.terms.position;

import cora.exceptions.IndexingError;
import cora.exceptions.NullInitialisationError;

public record MetaPos(int index, Position tail) implements Position {
  public MetaPos(int index, Position tail) {
    if (index <= 0) {
      throw new IndexingError("MetaPos", "constructor", index, 1, 9999999);
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
}
