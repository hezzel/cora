package cora.terms;

import cora.exceptions.*;
import cora.types.Product;
import cora.types.Type;
import cora.types.TypeFactory;
import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.function.Executable;
import static org.junit.jupiter.api.Assertions.*;

class TupleTest {
  final Term _s = TermFactory.createVar(TypeFactory.intSort);
  final Term _t = TermFactory.createVar(TypeFactory.intSort);

  @Test
  public void testConstructWithNullListArgument() {
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(null);
    args.add(_s);
    Assertions.assertThrows(NullInitialisationError.class, () -> {
      new Tuple(null);
      new Tuple(args);
      new Tuple(_s, _t, null);
    });
  }

  @Test
  public void testConstructWithTooShortArgument() {
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(_t);
    Assertions.assertThrows(IllegalArgumentError.class, () -> {
      new Tuple(args);
      new Tuple(new ArrayList<Term>());
    });
  }

  @Test
  public void testWellbehaved() {
    Variable x = TermFactory.createBinder("x", TypeFactory.createSort("a"));
    Term abs = TermFactory.createAbstraction(x, x);
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(abs);
    args.add(x);
    Tuple tuple = new Tuple(args);
    Assertions.assertTrue(args.get(0) == abs);
    assertTrue(args.get(1) == x);
    Variable y = tuple.queryTupleArgument(1).queryVariable();
    assertTrue(y != null);
    assertTrue(y != x);
    System.out.println(tuple.toString());
    ReplaceableList fr = tuple.freeReplaceables();
    assertTrue(tuple.vars().contains(x));
    assertTrue(tuple.boundVars().contains(y));
    assertTrue(tuple.toString().equals("⦅λx1.x1, x⦆"));
  }



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
