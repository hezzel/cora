package cora.terms;

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.function.Executable;
import static org.junit.jupiter.api.Assertions.*;
import cora.exceptions.*;
import cora.utils.Pair;
import cora.types.Product;
import cora.types.Type;
import cora.types.TypeFactory;
import cora.terms.position.*;

class TupleTest extends TermTestFoundation {
  final Term _s = TermFactory.createVar(TypeFactory.intSort);
  final Term _t = TermFactory.createVar(TypeFactory.intSort);

  @Test
  public void testConstructWithNullListArgument() {
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(null);
    args.add(_s);
    Assertions.assertThrows(NullInitialisationError.class, () -> new Tuple(null));
    Assertions.assertThrows(NullInitialisationError.class, () -> new Tuple(args));
    Assertions.assertThrows(NullInitialisationError.class, () -> new Tuple(_s, _t, null));
  }

  @Test
  public void testConstructWithTooShortArgumentList() {
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(_t);
    Assertions.assertThrows(IllegalArgumentError.class, () -> new Tuple(args));
    Assertions.assertThrows(IllegalArgumentError.class, () -> new Tuple(new ArrayList<Term>()));
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
    ReplaceableList fr = tuple.freeReplaceables();
    assertTrue(tuple.vars().contains(x));
    assertTrue(tuple.boundVars().contains(y));
    assertTrue(tuple.toString().equals("⦇λx1.x1, x⦈"));
  }

  private Term exampleTuple() {
    Term a = new Constant("a", baseType("N"));
    Variable x = new Binder("x", baseType("N"));
    Term abs = new Abstraction(x, unaryTerm("f", baseType("M"), x));
    Variable y = new Var("y", baseType("P"));
    Variable z = new Var("z", arrowType("P", "P"));
    Term fa = unaryTerm("f", baseType("M"), a);
    return new Tuple(a, abs, new Tuple(fa, y));
  }

  @Test
  public void testBasics() {
    Term tuple = exampleTuple();
    Variable y = new Var("y", baseType("P"));
    Variable z = new Var("z", arrowType("P", "P"));
    Term a = constantTerm("a", baseType("A"));
    Term tuple2 = new Tuple(y, z.apply(y));
    Term tuple3 = new Tuple(a, unaryTerm("f", baseType("A"), a));
    Term tuple4 = new Tuple(new IntegerValue(3), new BooleanValue(false));

    assertTrue(tuple.toString().equals("⦇a, λx.f(x), ⦇f(a), y⦈⦈"));
    assertTrue(tuple.queryType().toString().equals("N × (N ⇒ M) × (M × P)"));
    assertFalse(tuple.isVariable());
    assertFalse(tuple2.isVariable());
    assertFalse(tuple.isConstant());
    assertFalse(tuple.isFunctionalTerm());
    assertFalse(tuple.isVarTerm());
    assertFalse(tuple.isApplication());
    assertFalse(tuple.isApplicative());
    assertTrue(tuple2.isApplicative());
    assertFalse(tuple.isAbstraction());
    assertFalse(tuple.isMetaApplication());
    assertTrue(tuple.isTuple());
    assertFalse(tuple.isBetaRedex());
    assertFalse(tuple.isGround());
    assertTrue(tuple3.isGround());
    assertTrue(tuple.isClosed());
    assertTrue(tuple.isTrueTerm());
    assertFalse(tuple.isValue());
    assertFalse(tuple4.isValue());

    assertTrue(tuple.queryHead() == tuple);
    assertTrue(tuple4.toValue() == null);
  }

  @Test
  void testIsTheoryTerm() {
    Term tp = exampleTuple();
    assertFalse(tp.isTheoryTerm());
    tp = new Tuple(_s, new Tuple(_t, new IntegerValue(12)));
    Assertions.assertTrue(tp.isTheoryTerm());
    Assertions.assertTrue(tp.queryType().isTheoryType());
  }

  @Test
  public void testFirstOrder() {
    Term tp = exampleTuple();
    assertFalse(tp.isFirstOrder());
    tp = new Tuple(_s, _s);
    assertTrue(tp.isFirstOrder());
    tp = new Tuple(new Tuple(_s, _t), _s);
    assertTrue(tp.isFirstOrder());
    tp = new Tuple(new Var("x", arrowType("a", "b")), _t);
    assertFalse(tp.isFirstOrder());
  }

  @Test
  public void testIsPattern() {
    assertTrue(exampleTuple().isPattern());
    Term z = new Var("Z", arrowType("a", "a"));
    Term tp = new Tuple(_s, new Application(z, constantTerm("A", baseType("a"))));
    assertFalse(tp.isPattern());
  }

  @Test
  public void testArguments() {
    Term tuple = exampleTuple();

    assertTrue(tuple.numberArguments() == 0);
    assertTrue(tuple.numberMetaArguments() == 0);
    assertTrue(tuple.numberTupleArguments() == 3);

    assertTrue(tuple.queryArguments().size() == 0);
    assertTrue(tuple.queryMetaArguments().size() == 0);

    List<Term> args = tuple.queryTupleArguments();
    assertTrue(args.size() == 3);
    assertTrue(args.get(0).toString().equals("a"));
    assertTrue(args.get(1).toString().equals("λx.f(x)"));
    assertTrue(args.get(2).isTuple());

    assertTrue(tuple.queryTupleArgument(1) == args.get(0));
    assertTrue(tuple.queryTupleArgument(2) == args.get(1));
    assertTrue(tuple.queryTupleArgument(3).queryTupleArgument(2).isVariable());

    Assertions.assertThrows(IndexingError.class, () -> tuple.queryArgument(1));
    Assertions.assertThrows(IndexingError.class, () -> tuple.queryMetaArgument(1));
  }

  @Test
  void testMethodsThatShouldAlwaysThrowError() {
    Term tp = exampleTuple();
    Tuple x = new Tuple(constantTerm("a", arrowType("A", "A")),
                        constantTerm("b", arrowType("A", "B")));
    Assertions.assertThrows(InappropriatePatternDataError.class,
      () -> tp.queryAbstractionSubterm());
    Assertions.assertThrows(InappropriatePatternDataError.class,
      () -> tp.queryRoot());
    Assertions.assertThrows(InappropriatePatternDataError.class,
      () -> tp.queryVariable());
    Assertions.assertThrows(InappropriatePatternDataError.class,
      () -> tp.queryMetaVariable());
    Assertions.assertThrows(ArityError.class,
      () -> x.apply(constantTerm("u", baseType("A"))));
  }

  @Test
  public void testPositionsAndSubterms() {
    Term tp = exampleTuple();
    assertTrue(tp.queryImmediateHeadSubterm(0) == tp);
    Assertions.assertThrows(IndexingError.class,
      () -> tp.queryImmediateHeadSubterm(1));
    List<Position> positions = tp.queryPositions(false);
    assertTrue(positions.toString().equals(
      "[1.ε, 2.0.1.ε, 2.0.ε, 2.ε, 3.1.1.ε, 3.1.ε, 3.2.ε, 3.ε, ε]"));
    assertTrue(tp.querySubterm(Position.parse("3.1")).toString().equals("f(a)"));
    assertTrue(tp.querySubterm(Position.parse("2.0*1")).toString().equals("f"));
    Term t = tp.replaceSubterm(positions.get(0), constantTerm("b", baseType("N")));
    assertTrue(t.toString().equals("⦇b, λx.f(x), ⦇f(a), y⦈⦈"));
    assertTrue(tp.toString().equals("⦇a, λx.f(x), ⦇f(a), y⦈⦈"));
    t = tp.replaceSubterm(Position.parse("3.1*1"), new Var("Z", arrowType("N", "M")));
    assertTrue(t.toString().equals("⦇a, λx.f(x), ⦇Z(a), y⦈⦈"));
    assertThrows(TypingError.class,
      () -> tp.replaceSubterm(positions.get(0), constantTerm("b", baseType("A"))));
    assertThrows(TypingError.class, () ->
      tp.replaceSubterm(Position.parse("3.1*1"), new Var("Z", arrowType("N", "A"))));
  }

  @Test
  public void testBadPositions() {
    Term tup = exampleTuple();
    assertThrows(IndexingError.class, () -> tup.querySubterm(Position.parse("4")));
    assertThrows(IndexingError.class, () -> tup.querySubterm(Position.parse("3.3")));
    assertThrows(IndexingError.class, () -> tup.querySubterm(Position.parse("3*1")));
    assertThrows(IndexingError.class, () -> tup.querySubterm(Position.parse("*1")));
    Term replacement = constantTerm("a", baseType("N"));
    assertThrows(IndexingError.class,
      () -> tup.replaceSubterm(Position.parse("4"), replacement));
    assertThrows(IndexingError.class,
      () -> tup.replaceSubterm(Position.parse("3.3"), replacement));
    assertThrows(IndexingError.class,
      () -> tup.replaceSubterm(Position.parse("3*1"), replacement));
  }

  @Test
  public void testSubstitution() {
    Term s = exampleTuple();
    Variable y = s.queryTupleArgument(3).queryTupleArgument(2).queryVariable();
    Substitution gamma = new Subst(y, constantTerm("q", baseType("P")));
    Term t = s.substitute(gamma);
    assertTrue(s.toString().equals("⦇a, λx.f(x), ⦇f(a), y⦈⦈"));
    assertTrue(t.toString().equals("⦇a, λx.f(x), ⦇f(a), q⦈⦈"));
  }

  @Test
  public void testMatch() {
    Variable x = new Var("X", baseType("A"));
    Variable y = new Var("Y", baseType("A"));
    Term tuple = new Tuple(x, y, x);

    Term a = constantTerm("a", baseType("A"));
    Term b = constantTerm("b", baseType("A"));
    Term c = constantTerm("c", baseType("A"));
    Substitution gamma;
    Term m;

    gamma = new Subst();
    assertTrue(tuple.match(a, gamma).equals(
      "a does not instantiate ⦇X, Y, X⦈ (not a tuple term)."));

    m = new Tuple(a, new Tuple(b, a));
    gamma = new Subst();
    assertTrue(tuple.match(m, gamma).equals(
      "⦇a, ⦇b, a⦈⦈ does not instantiate ⦇X, Y, X⦈ (mismatch on the tuple sizes)."));

    m = new Tuple(a, b, c);
    gamma = new Subst();
    assertTrue(tuple.match(m, gamma).equals("Variable X mapped both to a and to c."));

    m = new Tuple(a, b, a);
    gamma = new Subst();
    assertTrue(tuple.match(m, gamma) == null);
    assertTrue(gamma.get(x) == a);
    assertTrue(gamma.get(y) == b);
  }

  @Test
  public void testEquality() {
    Term a = exampleTuple();
    Term b = exampleTuple();
    // note that creating a variable twice gives different variables
    assertFalse(a.equals(b));
    Position pos = Position.parse("3.2");
    Term c = b.replaceSubterm(pos, a.querySubterm(pos));
    assertTrue(a.equals(c));
  }

  @Test
  public void testVariables() {
    Variable x = new Var("x", baseType("A"));
    MetaVariable y = TermFactory.createMetaVar("y", arrowType("A", "A"), 1);
    Variable z = new Binder("y", baseType("A"));
    Term meta = TermFactory.createMeta(y, z);
    Term tuple = new Tuple(x, meta, z);
    assertTrue(tuple.vars().size() == 2);
    assertTrue(tuple.vars().contains(x));
    assertTrue(tuple.vars().contains(z));
    assertTrue(tuple.mvars().size() == 2);
    assertTrue(tuple.mvars().contains(x.queryMetaVariable()));
    assertTrue(tuple.mvars().contains(y));
    assertTrue(tuple.freeReplaceables().size() == 3);
    assertTrue(tuple.freeReplaceables().contains(x));
    assertTrue(tuple.freeReplaceables().contains(y));
    assertTrue(tuple.freeReplaceables().contains(z));
  }
}
