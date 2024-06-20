package charlie.util.either;

import charlie.util.Pair;
import java.util.function.BinaryOperator;
import java.util.function.Function;

public class FunctorialUtils {

  public static <E, A> Either<E,A> pure(A value) {
    return new Right<>(value);
  }

  // TODO implement documentation
  public static <E, A, B> Function<Either<E, A>, Either<E,B>> fmap(Function<A,B> f) {
    return x -> x.map(f);
  }

  // TODO implement documentation
  public static <E, A> BinaryOperator<Either<E,A>> liftBinOp(BinaryOperator<A> op) {
    return (Either<E, A> x, Either<E, A> y) ->
      switch (new Pair<>(x, y) ) {
        case Pair(Left<E, A> _, _) -> x;
        case Pair(Right<E,A> _, Left<E,A> _), Pair(_, Left<E,A> _) -> y;
        case Pair(Right<E, A> l, Right<E,A> r) -> new Right<>(op.apply(l.value(), r.value()));
      };
  }

}
