package charlie.util.either;

import java.util.Objects;
import java.util.function.Consumer;
import java.util.function.Function;

public record Left<E,A>(E value) implements Either<E,A> {

  public Left(E value) {
    Objects.requireNonNull(value);
    this.value = value;
  }

  @Override
  public boolean isLeft() { return true; }

  @Override
  public boolean isRight() { return false; }

  @Override
  public <B> Either<E,B> map(Function<? super A, ? extends B> function) {
    Objects.requireNonNull(function);
    return new Left<>(this.value);
  }

  @Override
  public void action(Consumer<? super A> action) {
    Objects.requireNonNull(action);
  }

  @Override
  public String toString() {
    return "Left(" + value + ")";
  }
}
