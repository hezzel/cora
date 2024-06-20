package charlie.util.either;

import java.util.function.Consumer;
import java.util.function.Function;

/**
 * The {@code Either} generic type represents values with two possibilities:
 * a value of type {@code Either A B} is either a container constructed by
 * {@code Left<A,B>}, which holds a value of type {@code A}, or
 * {@code Right<A,B>}, which holds a value of type {@code B}.
 *
 * @apiNote
 *
 * @param <E> the type of {@code Left} values
 * @param <A> the type of {@code Right} values
 */
public sealed interface Either<E,A> permits Left, Right {

  /**
   * Returns whether this is a left value.
   */
  public abstract boolean isLeft();

  /**
   * Returns whether this is a right value.
   */
  public abstract boolean isRight();

  /**
   * Maps a function over the right value.
   * If this value is a left its content is unaltered.
   *
   * @param function a <a href="package-summary.html#NonInterference">non-interfering</a>,
   *                   <a href="package-summary.html#Statelessness">stateless</a>
   *                   function to apply.
   *                 Notice that providing a stateful lambda for this method might result in
   *                 unexpected behavior.
   * @return a value of type {@code Either<A,B>}
   *
   * @apiNote
   * <p> Notice that even on the cases where this is a left value if a function of type
   * {@code Function<? super A, ? extends B>} is applied. The left value changes its type to
   * {@code Either<E,B>}. This is the intended behavior of how the
   * {@code Either} type is implemented as a functor.
   * </p>
   *
   * <p>
   *   The type {@code E} is usually meant to be an error type.
   *   We use the convention that non-error type is on the right.
   * </p>
   */
  <B> Either<E,B> map(Function<? super A,? extends B> function);

  /**
   * Performs an action on its value {@code v} if this is a {@code Right v}
   * @param action a <a href="package-summary.html#NonInterference">
   *               non-interfering</a> action to perform on the right value
   */
  void action(Consumer<? super A> action);

  // TODO Add those functions to the interface and implement them.
//  <C> Either<A,B> mapLeft(Function<? super A, ? extends C> function);
//
//
//  void actionLeft(Consumer<? super A> action);
}
