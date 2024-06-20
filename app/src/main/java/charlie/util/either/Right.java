package charlie.util.either;

import java.util.Objects;
import java.util.function.Consumer;
import java.util.function.Function;

public record Right<E, A>(A value) implements Either<E,A> {

  @Override
  public boolean isRight() { return true; }

  @Override
  public boolean isLeft() { return false; }

  public <B> Either<E, B> map(Function<? super A, ? extends B> function) {
    Objects.requireNonNull(function);

    return new Right<>(function.apply(value));
  }

  public void action(Consumer<? super A> action) {
    Objects.requireNonNull(action);
    action.accept(value);
  }

  @Override
  public String toString() {
    return "Right(" + value + ")";
  }
}
