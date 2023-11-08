package cora.types;

import cora.exceptions.NullInitialisationError;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class ArrowTest {
  private Base intType() {
    return new Base("Int");
  }

  private Base boolType() {
    return new Base("Bool");
  }

  @Test
  void testConstructedWithNull() {
    Assertions.assertThrows(NullInitialisationError.class, () -> {
      new Arrow(null, new Base(""));
      new Arrow(new Base(""), null);
    });
  }
}
