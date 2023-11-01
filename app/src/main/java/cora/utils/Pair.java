package cora.utils;

public record Pair<A,B>(A left, B right) {
  public A fst (){ return this.left; }
  public B snd () { return this.right; }
}