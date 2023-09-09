/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.terms;

import org.junit.Test;
import static org.junit.Assert.*;
import java.lang.Error;
import java.util.ArrayList;
import java.util.List;
import java.util.TreeMap;
import java.util.TreeSet;
import cora.exceptions.*;
import cora.types.Type;
import cora.types.TypeFactory;

public class AbstractionTest extends TermTestFoundation {
  @Test(expected = NullInitialisationError.class)
  public void testConstructWithNullBinder() {
    Term s = constantTerm("a", baseType("A"));
    new Abstraction(null, s);
  }

  @Test(expected = NullInitialisationError.class)
  public void testConstructWithNullSubterm() {
    Variable x = TermFactory.createBinder("x", baseType("o"));
    new Abstraction(x, null);
  }

  @Test(expected = IllegalTermError.class)
  public void testConstructWithIllegalBinder() {
    Variable x = TermFactory.createVar("x", baseType("o"));
    Term s = constantTerm("a", baseType("A"));
    new Abstraction(x, s);
  }

  @Test
  public void testReplaceables() {
    Variable x = TermFactory.createBinder("x", baseType("a"));
    Variable y = TermFactory.createBinder("y", baseType("b"));
    Term f = constantTerm("f", arrowType(baseType("a"), arrowType("b", "c")));
    Term fxy = new Application(f, x, y);
    Term abs = new Abstraction(x, fxy); // λx.f(x,y)
    assertTrue(abs.freeReplaceables().size() == 1);
    assertFalse(abs.freeReplaceables().contains(x));
    assertTrue(abs.freeReplaceables().contains(y));
    assertTrue(abs.boundVars().size() == 1);
    assertTrue(abs.boundVars().contains(x));
    assertFalse(abs.boundVars().contains(y));
  }

  @Test
  public void testWellbehavedness() {
    // λx.f(x, f(g(λx.x), g(λx.f(x,x))))
    Variable x = new Binder("x", baseType("o"));
    Term g = constantTerm("g", arrowType(arrowType("o", "o"), baseType("o")));
    Term f = constantTerm("f", arrowType(baseType("o"), arrowType("o", "o")));
    Term s = new Abstraction(x, new Application(f, x, new Application(f,
      new Application(g, new Abstraction(x, x)),
      new Application(g, new Abstraction(x, new Application(f, x, x))))));

    assertTrue(s.toString().equals("λx.f(x, f(g(λx1.x1), g(λx1.f(x1, x1))))"));
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
  public void testRenaming() {
    // λx.λy.λu.f(g(z2,u),z1,x) where x and u have the same name, and z1 and z2 too
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Variable z1 = new Binder("z", baseType("o"));
    Variable z2 = new Binder("z", baseType("o"));
    Variable u = new Binder("x", baseType("o"));
    Constant f = new Constant("f", arrowType(baseType("o"), arrowType(baseType("o"),
      arrowType("o", "o"))));
    Constant g = new Constant("g", arrowType(baseType("o"), arrowType("o", "o")));
    Term main = (new Application(f, new Application(g, z2, u), z1)).apply(x);
    Term abs = new Abstraction(x, new Abstraction(y, new Abstraction(u, main)));

    StringBuilder builder = new StringBuilder();
    TreeSet<String> set = new TreeSet<String>();
    TreeMap<Replaceable,String> renaming = new TreeMap<Replaceable,String>();

    assertTrue(abs.toString().equals("λx.λy.λx1.f(g(z__2, x1), z__1, x)"));

    builder.setLength(0);
    abs.addToString(builder, renaming, set);
    assertTrue(builder.toString().equals("λx.λy.λx1.f(g(z, x1), z, x)"));
    assertTrue(renaming.size() == 0);

    builder.setLength(0);
    set.add("x");
    renaming.put(y, "yy");
    abs.addToString(builder, renaming, set);
    assertTrue(builder.toString().equals("λx1.λy.λx2.f(g(z, x2), z, x1)"));
    assertTrue(renaming.size() == 0);

    builder.setLength(0);
    set.add("x");
    set.add("x1");
    set.add("x2");
    set.add("y");
    set.add("y1");
    abs.addToString(builder, renaming, set);
    assertTrue(builder.toString().equals("λx3.λy2.λx4.f(g(z, x4), z, x3)"));
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
    assertTrue(main.toString().equals("λx.g(λx1.x1, h(x, x), λx1.f(x1))"));
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

    assertTrue(abs.queryType().toString().equals("(o ⇒ o) ⇒ b"));
    assertFalse(abs.isVariable());
    assertFalse(abs.isConstant());
    assertFalse(abs.isFunctionalTerm());
    assertFalse(abs.isVarTerm());
    assertFalse(abs.isApplication());
    assertFalse(abs.isApplicative());
    assertFalse(abs.isFirstOrder());
    assertTrue(abs.numberArguments() == 0);
    assertTrue(abs.numberMetaArguments() == 0);
    assertTrue(abs.queryArguments().size() == 0);
    assertTrue(abs.queryImmediateHeadSubterm(0) == abs);
    assertTrue(abs.queryAbstractionSubterm().toString().equals("f(x, λy.y)"));
    assertTrue(abs.queryHead() == abs);
    assertTrue(abs.queryVariable() == x);
    assertTrue(abs.isClosed());
    assertTrue(abs.isGround());
    assertFalse(abs.queryAbstractionSubterm().isClosed());
    assertFalse(abs.queryAbstractionSubterm().isGround());
    assertTrue(abs.isTrueTerm());
    assertFalse(abs.isValue());
    assertFalse(abs.isTheoryTerm());
    assertTrue(abs.apply(constantTerm("u", arrowType("o", "o"))).toString().equals(
      "(λx.f(x, λy.y))(u)"));
  }

  @Test
  public void testTheory() {
    // λx::Int.x + 1
    Variable x = new Binder("x", TypeFactory.intSort);
    Term abs = new Abstraction(x, new Application(new PlusSymbol(), x, new IntegerValue(1)));
    assertTrue(abs.toString().equals("λx.x + 1"));
    assertTrue(abs.isTheoryTerm());
    assertFalse(abs.isValue());
    assertTrue(abs.toValue() == null);

    // λy::o.0
    Variable y = new Binder("y", TypeFactory.unitSort);
    abs = new Abstraction(y, new IntegerValue(0));
    assertFalse(abs.isTheoryTerm());
  }

  @Test(expected = IndexingError.class)
  public void testImmediateHeadSubterm() {
    Term term = makeTerm(new Binder("x", baseType("o")));
    term.queryImmediateHeadSubterm(1);
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testRoot() {
    Term term = makeTerm(new Binder("x", baseType("o")));
    term.queryRoot();
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
    // λz.f(x(y), z) -- still a pattern, even though it's now not a bound variable that is applied
    s = new Abstraction(z, new Application(f, x.apply(y), z));
    assertTrue(s.isPattern());
    // λz.f(u(z), y) -- not a pattern, as a free variable is applied
    s = new Abstraction(z, new Application(f, u.apply(z), y));
    assertFalse(s.isPattern());
  }

  @Test
  public void testPositions() {
    // λx.f(x, λy.y)
    Variable x = new Binder("x", arrowType("a", "b"));
    Term term = makeTerm(x);
    List<Path> posses = term.queryPositions();

    assertTrue(posses.size() == 5);
    assertTrue(posses.get(0).toString().equals("0.1.ε"));
    assertTrue(posses.get(0).queryCorrespondingSubterm() == x);
    assertTrue(posses.get(0).queryAssociatedTerm() == term);
    assertTrue(posses.get(1).toString().equals("0.2.0.ε"));
    assertTrue(posses.get(1).queryAssociatedTerm() == term);
    assertTrue(posses.get(2).toString().equals("0.2.ε"));
    assertTrue(posses.get(1).queryCorrespondingSubterm() ==
               posses.get(2).queryCorrespondingSubterm().queryVariable());
    assertTrue(posses.get(3).toString().equals("0.ε"));
    assertTrue(posses.get(4).isEmpty());

    // (λx.f(x, λy.y))(A)
    Term a = constantTerm("A", arrowType("a", "b"));
    Term s = new Application(term, a);
    List<Path> subposses = term.queryPositionsForHead(s);

    assertTrue(subposses.size() == 4);
    assertTrue(subposses.get(0).toString().equals("0.1.ε"));
    assertTrue(subposses.get(0).queryCorrespondingSubterm() == x);
    assertTrue(subposses.get(0).queryAssociatedTerm() == s);
    assertTrue(subposses.get(2).toString().equals("0.2.ε"));
    assertTrue(subposses.get(3).queryAssociatedTerm() == s);
  }

  @Test
  public void testHeadPositions() {
    // λx.f(x, λy.y)
    Variable x = new Binder("x", arrowType("a", "b"));
    Term term = makeTerm(x);
    List<HeadPosition> posses = term.queryHeadPositions();
    assertTrue(posses.size() == 7);
    assertTrue(posses.get(0).toString().equals("0.1.ε"));
    assertTrue(posses.get(1).toString().equals("0.2.0.ε"));
    assertTrue(posses.get(2).toString().equals("0.2.ε"));
    assertTrue(posses.get(3).toString().equals("0.☆2"));
    assertTrue(posses.get(4).toString().equals("0.☆1"));
    assertTrue(posses.get(5).toString().equals("0.ε"));
    assertTrue(posses.get(6).isEnd() && posses.get(6).queryChopCount() == 0);
  }

  @Test
  public void testQuerySubtermGood() {
    // λx.f(x, λy.y)
    Variable x = new Binder("x", baseType("o"));
    Term term = makeTerm(x);
    assertTrue(term.querySubterm(PositionFactory.parsePos("0.1")) == x);
    assertTrue(term.querySubterm(PositionFactory.parsePos("0.2")).toString().equals("λy.y"));
  }

  @Test
  public void testQueryHeadSubtermGood() {
    Variable x = new Binder("x", baseType("o"));
    Term term = makeTerm(x);
    HeadPosition pos = PositionFactory.parseHPos("0.☆1");
    assertTrue(term.querySubterm(pos).toString().equals("f(x)"));
  }

  @Test(expected = IndexingError.class)
  public void testArgumentPositionRequest() {
    Term term = makeTerm(new Binder("x", baseType("o")));
    term.querySubterm(PositionFactory.parsePos("1.ε"));
  }

  @Test(expected = IndexingError.class)
  public void testHeadPositionRequest() {
    Term term = makeTerm(new Binder("x", baseType("o")));
    term.querySubterm(PositionFactory.parseHPos("1.2.☆1"));
  }

  @Test
  public void testReplaceSubtermGood() {
    Term h = constantTerm("h", arrowType("a", "a"));
    Variable x = new Binder("x", baseType("b"));
    Variable y = new Binder("y", baseType("b"));
    Term term = makeTerm(x);
    Term term1 = term.replaceSubterm(PositionFactory.parsePos("0.2"), h);
    Term term2 = term.replaceSubterm(PositionFactory.parsePos("0.1"), y);
    Term term3 = term.replaceSubterm(PositionFactory.parsePos("0"), x);
    assertTrue(term1.toString().equals("λx.f(x, h)"));
    assertTrue(term2.toString().equals("λx.f(y, λy1.y1)"));
    assertTrue(term3.equals(new Abstraction(x, x)));
  }

  @Test(expected = IndexingError.class)
  public void testBadPositionReplacement() {
    Term term = makeTerm(new Binder("x", baseType("o")));
    term.replaceSubterm(PositionFactory.parsePos("1"), constantTerm("a", baseType("o")));
  }

  @Test(expected = TypingError.class)
  public void testBadTypeReplacement() {
    Term term = makeTerm(new Binder("x", baseType("o")));
    term.replaceSubterm(PositionFactory.parsePos("0.2"), constantTerm("a", baseType("o")));
  }

  @Test
  public void testReplaceHeadSubtermGood() {
    Term term = makeTerm(new Binder("x", baseType("o")));
    Term h = constantTerm("h", arrowType(arrowType("a", "a"), baseType("b")));
    Term a = constantTerm("A", arrowType("o", "b"));
    Term term1 = term.replaceSubterm(PositionFactory.parseHPos("0.*1"), h);
    Term term2 = term.replaceSubterm(PositionFactory.parseHPos("ε"), a);
    assertTrue(term1.toString().equals("λx.h(λy.y)"));
    assertTrue(term2.equals(a));
  }

  @Test(expected = IndexingError.class)
  public void testReplaceHeadOfAbstraction() {
    Term term = makeTerm(new Binder("x", baseType("o")));
    term.replaceSubterm(PositionFactory.parseHPos("*1"), constantTerm("a", baseType("o")));
  }

  @Test(expected = IndexingError.class)
  public void testNonexistentInternalHeadPosition() {
    Term term = makeTerm(new Binder("x", baseType("o")));
    term.replaceSubterm(PositionFactory.parseHPos("0.0"), constantTerm("a", baseType("o")));
  }

  @Test(expected = IndexingError.class)
  public void testNonexistingHeadPosition() {
    Term term = makeTerm(new Binder("x", baseType("o")));
    term.replaceSubterm(PositionFactory.parseHPos("1"), constantTerm("a", baseType("b")));
  }

  @Test(expected = TypingError.class)
  public void testReplaceHeadWithIlltyped() {
    Term term = makeTerm(new Binder("x", baseType("o")));
    term.replaceSubterm(PositionFactory.parseHPos("ε"), constantTerm("a", baseType("b")));
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
    assertTrue(s.toString().equals(abs.toString()));
    Variable a = s.queryVariable();
    Variable b = s.queryAbstractionSubterm().queryArgument(2).queryVariable();
    assertTrue(a.compareTo(u) == 1);
    assertTrue(b.compareTo(u) == 1);
    assertFalse(a.equals(b));
  }

  @Test
  public void testSubstitute() {
    // λx.f(x, λz.z, y)
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Var("y", baseType("o"));
    Variable z = new Binder("z", baseType("o"));
    Variable u = new Binder("u", baseType("o"));
    Term f = constantTerm("f", arrowType(baseType("o"), arrowType(
      arrowType("o", "o"), arrowType("o", "o"))));
    Term abs = new Abstraction(x, new Application(new Application(f, x,
      new Abstraction(z, z)), y));

    // [x:=y, y:=x]
    Substitution subst = new Subst();
    subst.extend(x, y);
    subst.extend(y, x);
    Term term = abs.substitute(subst);  // now term = λu.f(u, λz.z, x)

    // check that we got the right term
    assertFalse(term.equals(abs));
    assertTrue(term.equals(new Abstraction(u, new Application(
      new Application(f, u, new Abstraction(z, z)), x))));
    assertTrue(term.toString().equals("λx1.f(x1, λz.z, x)"));

    // check that all binders are fresh
    assertTrue(term.queryVariable().compareTo(u) == 1);
    assertTrue(term.queryAbstractionSubterm().queryArgument(2).queryVariable().compareTo(u) == 1);
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
    assertTrue(term.match(m, gamma) == null);
    assertTrue(gamma.get(x) == null);
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
    assertTrue(term.match(m, gamma) == null);
    assertTrue(gamma.get(x) == null);
    assertTrue(gamma.get(y) == null);
    assertTrue(gamma.get(z) == z);
    assertTrue(gamma.get(f).toString().equals("λz.λy.h(a(y), z)"));
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

    assertTrue(term.match(m1, new Subst()) == null);
    assertTrue(term.match(m2, new Subst()) != null);
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

    // after a check, the size and contents of mu and xi are unaltered
    assertTrue(mu.size() == 1);
    assertTrue(mu.get(y) == 1);
    assertFalse(mu.containsKey(x));
    assertTrue(xi.size() == 1);
    assertTrue(xi.get(u) == 1);
    assertFalse(xi.containsKey(x));
    assertFalse(xi.containsKey(z));

    // there is no issue if x is in xi, or z in mu
    mu.put(z, 2);
    xi.put(x, 3);
    assertTrue(s.alphaEquals(t, mu, xi, 4));
  }

  @Test(expected = IllegalTermError.class)
  public void testBinderAlreadyInMu() {
    Variable x = new Binder("x", baseType("o"));
    Term term = new Abstraction(x, x);
    TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
    TreeMap<Variable,Integer> xi = new TreeMap<Variable,Integer>();
    mu.put(x, 1);
    term.alphaEquals(term, mu, xi, 2);
  }

  @Test(expected = IllegalTermError.class)
  public void testBinderAlreadyInXi() {
    Variable x = new Binder("x", baseType("o"));
    Term term = new Abstraction(x, x);
    TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
    TreeMap<Variable,Integer> xi = new TreeMap<Variable,Integer>();
    xi.put(x, 1);
    term.alphaEquals(term, mu, xi, 2);
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

}

