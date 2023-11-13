package cora.terms;

import com.google.common.collect.ImmutableList;
import cora.exceptions.IllegalArgumentError;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.TypingError;
import cora.types.Product;
import cora.types.Type;
import cora.types.TypeFactory;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.function.Executable;

import java.util.List;

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

  @Test
  void testPositions(){
    Term tp = new Tuple(ImmutableList.of(_s, _t));
    System.out.println(tp.queryPositions());
    System.out.println(tp);
  }

  @Test
  void testReplacement(){
    Term tp = new Tuple(ImmutableList.of(_s, _t, TermFactory.createVar(TypeFactory.boolSort)));
    Term tp2 = new Tuple(ImmutableList.of(_t, _s));
    List<Path> paths = tp.queryPositions();
    System.out.println(paths);
    System.out.println(paths.get(0).queryComponentPosition());

    Position p = PositionFactory.empty;
    Assertions.assertThrows(TypingError.class,
      () -> tp.replaceSubterm(p, _s)
    );

    System.out.println(tp + " of type " + tp.queryType());

    Term newVar = TermFactory.createVar(TypeFactory.intSort);

    Term rep = tp.replaceSubterm(paths.get(0), newVar);

    System.out.println(rep);


  }


}
