package cora.terms;

import com.google.common.collect.ImmutableList;
import cora.exceptions.IllegalArgumentError;
import cora.exceptions.InappropriatePatternDataError;
import cora.types.TypeFactory;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.function.Executable;

class TupleTest {

  Term _s = TermFactory.createVar(TypeFactory.intSort);
  Term _t = TermFactory.createVar(TypeFactory.intSort);


  @Test
  void testArgumentLength() {
  // building tuples with less than two elements should throw IllegalArgumentError
    Assertions.assertThrows(IllegalArgumentError.class,
      () -> new Tuple(ImmutableList.of())
    );

    Assertions.assertThrows(IllegalArgumentError.class,
      () -> new Tuple(ImmutableList.of(_s))
    );
  }

  @Test
  void testIsTheoryTermComposition() {
    Term tp = new Tuple(ImmutableList.of(_s, _t));

    Assertions.assertTrue(tp.isTheoryTerm());
    Assertions.assertTrue(tp.queryType().isTheoryType());
  }

  @Test
  void testMethodsThatShouldAlwaysThrowError() {
    Term tp = new Tuple(ImmutableList.of(_s, _t));
    Assertions.assertThrows(InappropriatePatternDataError.class,
      () -> tp.queryAbstractionSubterm()
    );

  }

}
