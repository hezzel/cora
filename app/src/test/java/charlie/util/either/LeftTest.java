package charlie.util.either;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.*;

class LeftTest {

  @Test
  void isLeft() {

    Either<String, Boolean> right = new Right<>(false);

    Function<Integer, Boolean> g = x -> x > 0;

    Either<Integer, Integer> val = new Left<>(3);

    Either<?,Boolean> valOfG = val.map(g);


  }

  @Test
  void isRight() {
  }

  @Test
  void value() {
  }
}
