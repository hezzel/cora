package cora.terms.position;

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
}
