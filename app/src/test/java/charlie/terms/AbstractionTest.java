/**************************************************************************************************
 Copyright 2023-2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.terms;

import java.util.List;
import java.util.HashMap;
import java.util.TreeMap;
import java.util.TreeSet;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.util.Pair;
import charlie.util.NullStorageException;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.position.PositionFormatException;
import charlie.terms.position.Position;

class AbstractionTest extends TermTestFoundation {
  @Test
  void testConstructorsNullInitialization() {
    // Abstractions with null binders should throw NullInitializationException
    assertThrows(NullStorageException.class, () ->
      new Abstraction(null,
        TermFactory.createConstant("a", TypeFactory.createSort("A"))
      )
    );
    // Abstractions with null body should throw NullInitializationException
    assertThrows(NullStorageException.class, () ->
      new Abstraction(
        TermFactory.createVar("x", TypeFactory.createSort("o")),
        null
      )
    );
  }

  @Test
  void testConstructorWithIllegalBinder() {
    assertThrows(IllegalArgumentException.class, () ->
      new Abstraction(
        TermFactory.createVar("x", TypeFactory.createSort("o")),
        TermFactory.createConstant("a", TypeFactory.createSort("A"))
      )
    );
  }

  @Test
  public void testReplaceables() {
    Type sortA = TypeFactory.createSort("a");
    Type sortB = TypeFactory.createSort("b");
    Type sortC = TypeFactory.createSort("c");
    Type arrTy = TypeFactory.createArrow(sortA, TypeFactory.createArrow(sortB, sortC));

    Variable x = TermFactory.createBinder("x", sortA);
    Variable y = TermFactory.createBinder("y", sortB);

    Term f = TermFactory.createConstant("f", arrTy);
    Term fxy = new Application(f, x, y);
    Term abs = new Abstraction(x, fxy); // λx.f(x,y)

    assertEquals(1, abs.freeReplaceables().size());
    assertFalse(abs.freeReplaceables().contains(x));
    assertTrue(abs.freeReplaceables().contains(y));
    assertEquals(1, abs.boundVars().size());
    assertTrue(abs.boundVars().contains(x));
    assertFalse(abs.boundVars().contains(y));
  }

  @Test
  void testWellbehavedness() {
    // λx.f(x, f(g(λx.x), g(λx.f(x,x))))
    Variable x = new Binder("x", baseType("o"));
    Term g = constantTerm("g", arrowType(arrowType("o", "o"), baseType("o")));
    Term f = constantTerm("f", arrowType(baseType("o"), arrowType("o", "o")));
    Term s = new Abstraction(x, new Application(f, x, new Application(f,
      new Application(g, new Abstraction(x, x)),
      new Application(g, new Abstraction(x, new Application(f, x, x))))));

    assertEquals("λx.f(x, f(g(λx1.x1), g(λx1.f(x1, x1))))", s.toString());
    Variable x1 = s.queryVariable();
    Term body = s.queryAbstractionSubterm();
    Term abs1 = body.queryArgument(2).queryArgument(1).queryArgument(1);  // λx1.x1
    Term abs2 = body.queryArgument(2).queryArgument(2).queryArgument(1);  // λx1.f(x1, x1)
    Variable x2 = abs1.queryVariable();
    Variable x3 = abs2.queryVariable();

    assertTrue(x1.equals(body.queryArgument(1).queryVariable()));
    assertTrue(x2.equals(abs1.queryAbstractionSubterm().queryVariable()));
    assertTrue(x3.equals(abs2.queryAbstractionSubterm().queryArgument(2).queryVariable()));

    assertFalse(x1.equals(x2));
    assertFalse(x1.equals(x3));
    assertFalse(x2.equals(x3));
    assertTrue(x1.equals(x));
  }

  @Test
  public void testNoRefreshWhenNotNeeded() {
    // λx.f(λy.y, x)
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("x", baseType("o"));
    Term f = constantTerm("f", arrowType(arrowType("o", "o"), arrowType("o", "o")));
    Term term = new Abstraction(x, new Application(f, new Abstraction(y, y), x));
    assertTrue(term.queryVariable() == x);
    assertTrue(term.queryAbstractionSubterm().queryArgument(1).queryVariable() == y);
  }

  @Test
  public void testToStringBasics() {
    Variable x = new Binder("x", baseType("o"));
    Term s = unaryTerm("f", baseType("a"), x);
    Term abs = new Abstraction(x, s);
    assertTrue(abs.toString().equals("λx.f(x)"));
    Variable y = new Binder("y", baseType("a"));
    abs = new Abstraction(y, abs);
    assertTrue(abs.toString().equals("λy.λx.f(x)"));
  }

  @Test
  public void testToStringComplex() {
    Variable x1 = new Binder("x", baseType("o"));
    Variable x2 = new Binder("x", baseType("o"));
    Variable x3 = new Binder("x", baseType("o"));
    Term f = constantTerm("f", arrowType("o", "o"));
    Term g = constantTerm("g", arrowType(arrowType("o", "o"),
      arrowType(baseType("o"), arrowType(arrowType("o", "o"), baseType("o")))));
    Term h = constantTerm("h", arrowType(baseType("o"), arrowType("o", "o")));
    Term abs1 = new Abstraction(x1, f.apply(x1));
    Term abs2 = new Abstraction(x2, x2);
    Term s = (new Application(g, abs2, new Application(h, x3, x3))).apply(abs1);
    Term main = new Abstraction(x3, s); // λx.g(λx.x, h(x, x), λx.f(x))
    assertEquals("λx.g(λx1.x1, h(x, x), λx1.f(x1))", main.toString());
  }

  /* @return λx.f(x, λy.y) */
  private Term makeTerm(Variable x) {
    Variable y = new Binder("y", baseType("a"));
    Constant f = new Constant("f", arrowType(x.queryType(), arrowType(
      arrowType("a", "a"), baseType("b"))));
    return new Abstraction(x, new Application(f, x, new Abstraction(y, y)));
  }

  @Test
  public void testBasics() {
    // λx.f(x, λy.y)
    Variable x = new Binder("x", arrowType("o", "o"));
    Term abs = makeTerm(x);

    assertEquals("(o → o) → b", abs.queryType().toString());
    assertFalse(abs.isVariable());
    assertFalse(abs.isConstant());
    assertFalse(abs.isFunctionalTerm());
    assertFalse(abs.isVarTerm());
    assertFalse(abs.isApplication());
    assertFalse(abs.isApplicative());
    assertFalse(abs.isFirstOrder());
    assertEquals(0, abs.numberArguments());
    assertEquals(0, abs.numberMetaArguments());
    assertEquals(0, abs.queryArguments().size());
    assertSame(abs.queryImmediateHeadSubterm(0), abs);
    assertEquals("f(x, λy.y)", abs.queryAbstractionSubterm().toString());
    assertSame(abs.queryHead(), abs);
    assertSame(abs.queryVariable(), x);
    assertTrue(abs.isClosed());
    assertTrue(abs.isGround());
    assertFalse(abs.queryAbstractionSubterm().isClosed());
    assertFalse(abs.queryAbstractionSubterm().isGround());
    assertTrue(abs.isTrueTerm());
    assertFalse(abs.isValue());
    assertFalse(abs.isTheoryTerm());
    assertTrue(abs.isLinear());
    assertEquals("(λx.f(x, λy.y))(u)", abs.apply(constantTerm("u", arrowType("o", "o"))).toString());
  }

  @Test
  public void testSymbols() {
    // λx.⦇ f(x, λy.y), λy.g(y) ⦈
    Variable x = new Binder("x", baseType("a"));
    Variable y = new Binder("y", baseType("b"));
    Constant f =
      new Constant("f", arrowType(baseType("a"), arrowType(arrowType("b", "b"), baseType("b"))));
    Constant g = new Constant("g", arrowType("b", "b"));
    Term abs1 = new Application(f, x, new Abstraction(y, y));
    Term abs2 = new Abstraction(y, new Application(g, y));
    Term abs = new Abstraction(x, new Tuple(abs1, abs2));
    TreeSet<FunctionSymbol> set = new TreeSet<FunctionSymbol>();
    abs.storeFunctionSymbols(set);
    assertTrue(set.contains(f));
    assertTrue(set.contains(g));
    assertTrue(set.size() == 2);
  }

  @Test
  public void testTheory() {
    // λx::Int.x + 1
    Variable x = new Binder("x", TypeFactory.intSort);
    Term abs = new Abstraction(x, new Application(TheoryFactory.plusSymbol, x, new IntegerValue(1)));
    assertEquals("λx.x + 1", abs.toString());
    assertTrue(abs.isTheoryTerm());
    assertFalse(abs.isValue());
    assertNull(abs.toValue());

    // λy::o.0
    Variable y = new Binder("y", TypeFactory.defaultSort);
    abs = new Abstraction(y, new IntegerValue(0));
    assertFalse(abs.isTheoryTerm());
  }

  @Test
  void testImmediateheadSubterm() {
    assertThrows(IndexOutOfBoundsException.class, () -> {
      Term term = makeTerm(new Binder("x", baseType("o")));
      term.queryImmediateHeadSubterm(1);
    });
  }

  @Test
  void testRoot() {
    assertThrows(InappropriatePatternDataException.class, () -> {
      Term term = makeTerm(new Binder("x", baseType("o")));
      term.queryRoot();
    });
  }

  @Test
  public void testPattern() {
    Term f = constantTerm("f", arrowType(baseType("o"), arrowType("o", "o")));
    Variable x = new Binder("x", arrowType("o", "o"));
    Variable y = new Var("y", baseType("o"));
    Variable z = new Binder("z", baseType("o"));
    Variable u = new Var("u", arrowType("o", "o"));
    // λx.f(x(z), y) -- pattern, because only a BINDER variable is applied
    // note that not all binder variables are bound, but this is not required
    Term s = new Abstraction(x, new Application(f, x.apply(z), y));
    assertTrue(s.isPattern());
    assertTrue(s.isSemiPattern());
    // λz.f(x(y), z) -- still a pattern, even though it's now not a bound variable that is applied
    s = new Abstraction(z, new Application(f, x.apply(y), z));
    assertTrue(s.isPattern());
    assertTrue(s.isSemiPattern());
    // λz.f(u(z), y) -- not a pattern, as a free variable is applied, but still a semi-pattern
    s = new Abstraction(z, new Application(f, u.apply(z), y));
    assertFalse(s.isPattern());
    assertTrue(s.isSemiPattern());
    // λz.F[u(z)] -- not a pattern or semi-pattern
    MetaVariable ff = TermFactory.createMetaVar("F", baseType("o"), baseType("o"));
    s = new Abstraction(z, TermFactory.createMeta(ff, u.apply(z)));
    assertFalse(s.isPattern());
    assertFalse(s.isSemiPattern());
  }

  @Test
  public void testQuerySubterms() {
    // λx.f(x, λy.y)
    Variable x = new Binder("x", arrowType("a", "b"));
    Term term = makeTerm(x);
    List<Pair<Term,Position>> subs = term.querySubterms();

    assertEquals(5, subs.size());
    assertEquals("0.1", subs.get(0).snd().toString());
    assertSame(subs.get(0).fst(), x);
    assertEquals("0.2.0", subs.get(1).snd().toString());
    assertEquals("0.2", subs.get(2).snd().toString());
    assertSame(subs.get(1).fst(), subs.get(2).fst().queryVariable());
    assertEquals("0", subs.get(3).snd().toString());
    assertTrue(subs.get(4).snd().isEmpty());
    // subterms below a binder are only acceptable if the bound variable does not occur free in them
    assertFalse(term.hasSubterm(subs.get(3).fst()));
    assertTrue(term.hasSubterm(subs.get(2).fst()));
  }

  @Test
  public void testQueryPositions() {
    // λx.f(x, λy.y)
    Variable x = new Binder("x", arrowType("a", "b"));
    Term term = makeTerm(x);

    List<Position> pos1 = term.queryPositions(false);
    List<Position> pos2 = term.queryPositions(true);
    
    assertTrue(pos1.toString().equals("[0.1, 0.2.0, 0.2, 0, ε]"));
    assertTrue(pos2.toString().equals("[0.1, 0.2.0, 0.2, 0.☆2, 0.☆1, 0, ε]"));
  }

  @Test
  public void testQuerySubtermGood() throws PositionFormatException {
    // λx.f(x, λy.y)
    Variable x = new Binder("x", baseType("o"));
    Term term = makeTerm(x);
    assertTrue(term.querySubterm(Position.parse("0.1")) == x);
    assertTrue(term.querySubterm(Position.parse("0.2")).toString().equals("λy.y"));
  }

  @Test
  public void testQueryPartialSubtermGood() throws PositionFormatException {
    Variable x = new Binder("x", baseType("o"));
    Term term = makeTerm(x);
    Position pos = Position.parse("0.☆1");
    assertTrue(term.querySubterm(pos).toString().equals("f(x)"));
  }

  @Test
  void testBadArgumentPositionRequest() throws PositionFormatException {
    assertThrows(InvalidPositionException.class, () -> {
      Term term = makeTerm(new Binder("x", baseType("o")));
      term.querySubterm(Position.parse("1.ε"));
    });
  }

  @Test
  void testBadPartialPositionRequest() throws PositionFormatException {
    assertThrows(InvalidPositionException.class, () -> {
      Term term = makeTerm(new Binder("x", baseType("o")));
      term.querySubterm(Position.parse("1.2.☆1"));
    });
  }

  @Test
  public void testReplaceSubtermGood() throws PositionFormatException {
    Term h = constantTerm("h", arrowType("a", "a"));
    Variable x = new Binder("x", baseType("b"));
    Variable y = new Binder("y", baseType("b"));
    Term term = makeTerm(x);
    Term term1 = term.replaceSubterm(Position.parse("0.2"), h);
    Term term2 = term.replaceSubterm(Position.parse("0.1"), y);
    Term term3 = term.replaceSubterm(Position.parse("0"), x);
    assertTrue(term1.toString().equals("λx.f(x, h)"));
    assertTrue(term2.toString().equals("λx.f(y, λy1.y1)"));
    assertTrue(term3.equals(new Abstraction(x, x)));
  }

  @Test
  void testBadPositionReplacement() throws PositionFormatException {
    assertThrows(InvalidPositionException.class, () -> {
      Term term = makeTerm(new Binder("x", baseType("o")));
      term.replaceSubterm(Position.parse("1"), constantTerm("a", baseType("o")));
    });
  }

  @Test
  void testBadTypeReplacement() throws PositionFormatException {
    assertThrows(TypingException.class, () -> {
      Term term = makeTerm(new Binder("x", baseType("o")));
      term.replaceSubterm(Position.parse("0.2"), constantTerm("a", baseType("o")));
    });
  }

  @Test
  public void testReplacePartialSubtermGood() throws PositionFormatException {
    Term term = makeTerm(new Binder("x", baseType("o")));
    Term h = constantTerm("h", arrowType(arrowType("a", "a"), baseType("b")));
    Term a = constantTerm("A", arrowType("o", "b"));
    Term term1 = term.replaceSubterm(Position.parse("0.*1"), h);
    Term term2 = term.replaceSubterm(Position.parse("ε"), a);
    assertEquals("λx.h(λy.y)", term1.toString());
    assertTrue(term2.equals(a));
  }

  @Test
  void testReplaceHeadOfAbstraction() throws PositionFormatException {
    assertThrows(InvalidPositionException.class, () -> {
      Term term = makeTerm(new Binder("x", baseType("o")));
      term.replaceSubterm(Position.parse("*1"), constantTerm("a", baseType("o")));
    });
  }

  @Test
  void testNonExistentInternalPartialPosition() throws PositionFormatException {
    assertThrows(InvalidPositionException.class, () -> {
      Term term = makeTerm(new Binder("x", baseType("o")));
      term.replaceSubterm(Position.parse("0.0"), constantTerm("a", baseType("o")));
    });
  }

  @Test
  void testNonExistingPartialPosition() throws PositionFormatException {
    assertThrows(InvalidPositionException.class, () -> {
      Term term = makeTerm(new Binder("x", baseType("o")));
      term.replaceSubterm(Position.parse("1"), constantTerm("a", baseType("b")));
    });
  }

  @Test
  void testReplaceHeadWithIllTyped() throws PositionFormatException {
    assertThrows(TypingException.class, () -> {
      Term term = makeTerm(new Binder("x", baseType("o")));
      term.replaceSubterm(Position.parse("ε"), constantTerm("a", baseType("b")));
    });
  }

  @Test
  public void testRefreshBinders() {
    // λx.f(x, λz.z, y)
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Var("y", baseType("o"));
    Variable z = new Binder("z", baseType("o"));
    Variable u = new Binder("u", baseType("o"));
    Term f = constantTerm("f", arrowType(baseType("o"), arrowType(
      arrowType("o", "o"), arrowType("o", "o"))));
    Term abs = new Abstraction(x, new Application(new Application(f, x,
      new Abstraction(z, z)), y));

    Term s = abs.refreshBinders();
    assertTrue(s.equals(abs));
    assertEquals(s.toString(), abs.toString());
    Variable a = s.queryVariable();
    Variable b = s.queryAbstractionSubterm().queryArgument(2).queryVariable();
    assertEquals(1, a.compareTo(u));
    assertEquals(1, b.compareTo(u));
    assertFalse(a.equals(b));
  }

  @Test
  public void testSuccessfulMatchFreeBecomesBound() {
    // λx.f(x, y)
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Constant f = new Constant("f", arrowType(baseType("o"), arrowType("o", "o")));
    Term term = new Abstraction(x, new Application(f, x, y));

    // λy.f(y, g(a))
    Term a = new Constant("a", baseType("o"));
    Term g = new Constant("g", arrowType("o", "o"));
    Term m = new Abstraction(y, new Application(f, y, g.apply(a)));

    Substitution gamma = new Subst();
    assertNull(term.match(m, gamma));
    assertNull(gamma.get(x));
    assertTrue(gamma.get(y).equals(g.apply(a)));
  }

  @Test
  public void testSuccessfulMatchSameBinder() {
    // λx.f(x, f(x, y))
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Constant f = new Constant("f", arrowType(baseType("o"), arrowType("o", "o")));
    Term term = new Abstraction(x, new Application(f, x, new Application(f, x, y)));

    // λx.f(x, f(x, a))
    Term a = new Constant("a", baseType("o"));
    Term m = new Abstraction(x, new Application(f, x, new Application(f, x, a)));

    Substitution gamma = new Subst();
    assertTrue(term.match(m, gamma) == null);
    assertTrue(gamma.get(x) == null);
    assertTrue(gamma.get(y).equals(a));
  }

  @Test
  public void testMatchSwitchVariables() {
    // λy.λx.f(x, z(y))
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Variable z = new Var("z", arrowType("o", "o"));
    Constant f = new Constant("f", arrowType(baseType("o"), arrowType("o", "o")));
    Term term = new Abstraction(y, new Abstraction(x, new Application(f, z.apply(y))));

    // λx.λy.f(y, f(a, x))
    Term a = new Constant("a", baseType("o"));
    Term m = new Abstraction(x, new Abstraction(y, new Application(f,
      new Application(f, a, x))));

    Substitution gamma = new Subst();
    assertTrue(term.match(m, gamma) == null);
    assertTrue(gamma.get(x) == null);
    assertTrue(gamma.get(y) == null);
    assertTrue(gamma.get(z).equals(f.apply(a)));
  }

  @Test
  public void testMatchNonAbstractionFails() {
    // λx.f(x, y)
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Constant f = new Constant("f", arrowType(baseType("o"), arrowType("o", "o")));
    Term term = new Abstraction(x, new Application(f, x, y));

    // Z
    Term z = new Var("Z", arrowType("o", "o"));

    Substitution gamma = new Subst();
    assertTrue(term.match(z, gamma) != null);
  }

  @Test
  public void testDoNotInstantiateBinder() {
    // λx.x
    Variable x = new Binder("x", baseType("o"));
    Term term = new Abstraction(x, x);

    // λx.y
    Variable y = new Binder("y", baseType("o"));
    Term m = new Abstraction(x, y);

    Substitution gamma = new Subst();
    assertTrue(term.match(m, gamma) != null);
  }

  @Test
  public void testDoNotInstantiateWithBinder() {
    // λx.y
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Term term = new Abstraction(x, y);

    // λx.x
    Term m = new Abstraction(x, x);

    Substitution gamma = new Subst();
    assertTrue(term.match(m, gamma) != null);
  }

  @Test
  public void testMatchBinderVariableMayNotOccurDeeperInRange() {
    // λx.f(x, y)
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Constant f = new Constant("f", arrowType(baseType("o"), arrowType("o", "o")));
    Term term = new Abstraction(x, new Application(f, x, y));

    // λz.f(z, g(z))
    Variable z = new Binder("z", baseType("o"));
    Constant g = new Constant("g", arrowType("o", "o"));
    Term m = new Abstraction(z, new Application(f, z, new Application(g, z)));

    Substitution gamma = new Subst();
    assertTrue(term.match(m, gamma) != null);
  }

  @Test
  public void testMatchWithMetaApplication() {
    // λx.g(F⟨z,x⟩)
    Variable x = new Binder("x", baseType("o"));
    Variable z = new Binder("z", baseType("o"));
    MetaVariable f =
      TermFactory.createMetaVar("F", arrowType(baseType("o"), arrowType("o", "o")), 2);
    Term g = constantTerm("g", arrowType("o", "o"));
    Term term = new Abstraction(x, g.apply(TermFactory.createMeta(f, z, x)));

    // λy.g(h(a(y), z))
    Variable y = new Binder("y", baseType("o"));
    Term a = constantTerm("a", arrowType("o", "o"));
    Term h = constantTerm("h", arrowType(baseType("o"), arrowType("o", "o")));
    Term m = new Abstraction(y, g.apply(new Application(h, a.apply(y), z)));

    Substitution gamma = new Subst();
    gamma.extend(z, z);
    assertNull(term.match(m, gamma));
    assertNull(gamma.get(x));
    assertNull(gamma.get(y));
    assertSame(gamma.get(z), z);
    assertEquals("λz.λy.h(a(y), z)", gamma.get(f).toString());
  }

  @Test
  public void testMatchWithPartialMetaApplication() {
    // λx.λy.F[x]
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    MetaVariable f = TermFactory.createMetaVar("Z", arrowType("o", "o"), 1);
    Term term = new Abstraction(x, new Abstraction(y, TermFactory.createMeta(f, x)));

    // λx.λy.h(x, z)
    Variable z = new Binder("z", baseType("o"));
    Term h = constantTerm("h", arrowType(baseType("o"), arrowType("o", "o")));
    Term m1 = new Abstraction(x, new Abstraction(y, new Application(h, x, z)));
    // λx.λy.h(x, y)
    Term m2 = new Abstraction(x, new Abstraction(y, new Application(h, x, y)));

    assertNull(term.match(m1, new Subst()));
    assertNotNull(term.match(m2, new Subst()));
  }

  @Test
  public void testAlphaEquals() {
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("u", baseType("o"));
    Variable z = new Binder("z", baseType("o"));
    Variable u = new Binder("u", baseType("o"));
    Term f = new Constant("f", arrowType(baseType("o"), arrowType("o", "o")));
    Term s = new Abstraction(x, new Application(f, x, y)); // λx.f(x, y)
    Term t = new Abstraction(z, new Application(f, z, u)); // λz.f(z, u)
    TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
    TreeMap<Variable,Integer> xi = new TreeMap<Variable,Integer>();

    // in principle they differ because y != u
    assertFalse(s.alphaEquals(t, mu, xi, 1));

    // but with the right renaming, they are alpha-equal
    mu.put(y, 1);
    xi.put(u, 1);
    assertTrue(s.alphaEquals(t, mu, xi, 2));
    assertFalse(s.hashCode() == t.hashCode());
    assertTrue(s.hashCode(mu) == t.hashCode(xi));

    // after a check, the size and contents of mu and xi are unaltered
    assertEquals(1, mu.size());
    assertEquals(1, (int) mu.get(y));
    assertFalse(mu.containsKey(x));
    assertEquals(1, xi.size());
    assertEquals(1, (int) xi.get(u));
    assertFalse(xi.containsKey(x));
    assertFalse(xi.containsKey(z));

    // there is no issue if x is in xi, or z in mu
    mu.put(z, 2);
    xi.put(x, 3);
    assertTrue(s.alphaEquals(t, mu, xi, 4));
  }

  @Test
  void testBinderAlreadyInMu() {
    assertThrows(IllegalArgumentException.class, () -> {
      Variable x = new Binder("x", baseType("o"));
      Term term = new Abstraction(x, x);
      TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
      TreeMap<Variable,Integer> xi = new TreeMap<Variable,Integer>();
      mu.put(x, 1);
      term.alphaEquals(term, mu, xi, 2);
    });
  }

  @Test
  void testBinderAlreadyInXi() {
    assertThrows(IllegalArgumentException.class, () -> {
      Variable x = new Binder("x", baseType("o"));
      Term term = new Abstraction(x, x);
      TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
      TreeMap<Variable,Integer> xi = new TreeMap<Variable,Integer>();
      xi.put(x, 1);
      term.alphaEquals(term, mu, xi, 2);
    });
  }

  @Test
  public void testEqualsWithDifferentBinderTypes() {
    Term a = constantTerm("q", baseType("o"));
    Variable x = new Binder("x", baseType("a"));
    Variable y = new Binder("x", baseType("b"));
    Term term1 = new Abstraction(x, a);
    Term term2 = new Abstraction(y, a);
    assertFalse(term1.equals(term2));
    assertTrue(term1.equals(new Abstraction(x, a)));
  }

  @Test
  public void testSimpleAlphaEquivalence() {
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Constant f = new Constant("f", arrowType(baseType("o"), arrowType("o", "o")));
    Term a = constantTerm("a", baseType("o"));
    Term fxa = new Application(f, x, a);
    Term fya = new Application(f, y, a);
    Term abs1 = new Abstraction(x, fxa);  // λx.f(x, a)
    Term abs2 = new Abstraction(y, fya);  // λy.f(y, a)

    assertTrue(abs1.equals(abs1));
    assertTrue(abs1.equals(abs2));
    assertTrue(abs1.hashCode() == abs2.hashCode());
  }

  @Test
  public void testSwitchingAlphaEquivalence() {
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Constant f = new Constant("f", arrowType(baseType("o"), arrowType("o", "o")));

    // λxy.f(x,f(x,y))
    Term fxy = new Application(f, x, y);
    Term abs1 = new Abstraction(x, new Abstraction(y, new Application(f, x, fxy)));
    // λyx.f(y,f(y,x))
    Term fyx = new Application(f, y, x);
    Term abs2 = new Abstraction(y, new Abstraction(x, new Application(f, y, fyx)));

    assertTrue(abs1.equals(abs2));
    assertTrue(abs1.hashCode() == abs2.hashCode());
  }

  @Test
  public void testNonEquivalenceWhereOnlyOneIsBound() {
    Variable x = new Binder("x", baseType("a"));
    Variable y = new Binder("y", baseType("b"));
    Abstraction abs1 = new Abstraction(x, x);
    Abstraction abs2 = new Abstraction(x, y);

    assertFalse(abs1.equals(abs2));
    assertFalse(abs2.equals(abs1));
  }

  @Test
  public void testHashCodeWithHashMap() {
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("u", baseType("o"));
    Variable z = new Binder("z", baseType("o"));
    Variable u = new Binder("u", baseType("o"));
    Term f = new Constant("f", arrowType(baseType("o"), arrowType("o", "o")));
    Term s = new Abstraction(x, new Application(f, x, y)); // λx.f(x, y)
    Term t = new Abstraction(z, new Application(f, z, u)); // λz.f(z, u)
    HashMap<Variable,Integer> mu = new HashMap<Variable,Integer>();
    TreeMap<Variable,Integer> xi = new TreeMap<Variable,Integer>();
    mu.put(y, 1);
    xi.put(u, 1);
    assertTrue(s.hashCode(mu) == t.hashCode(xi));
  }
}
