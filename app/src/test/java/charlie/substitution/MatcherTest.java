/**************************************************************************************************
 Copyright 2019--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.substitution;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import java.util.List;
import java.util.Set;

import charlie.util.NullStorageException;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.parser.CoraParser;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.MetaVariable;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.FunctionSymbol;
import charlie.terms.TypingException;
import charlie.terms.TermFactory;
import charlie.terms.TheoryFactory;

public class MatcherTest {
  private Type type(String str) {
    return CoraParser.readType(str);
  }

  private Term unaryTerm(String symbol, Term arg, String outtype) {
    Term f =
      TermFactory.createConstant(symbol, TypeFactory.createArrow(arg.queryType(), type(outtype)));
    return f.apply(arg);
  }

  @Test
  public void testNullMatch() {
    Term x = TermFactory.createVar("x", type("Int"));
    assertThrows(NullPointerException.class, () -> Matcher.match(null, x));
    assertThrows(NullPointerException.class, () -> Matcher.match(x, null));
    assertThrows(NullPointerException.class, () -> Matcher.extendMatch(x, x, null));
  }

  @Test
  public void testMatchUnknownVar() {
    Variable x = TermFactory.createVar("x", type("a"));
    Term t = unaryTerm("f", TermFactory.createConstant("u", type("b")), "a");
    Substitution gamma = Matcher.match(x, t);
    assertTrue(gamma.get(x) == t);
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testMatchKnownVar() {
    Variable x = TermFactory.createBinder("x", type("a"));
    Term t = unaryTerm("f", TermFactory.createConstant("u", type("b")), "a");
    MutableSubstitution gamma = new MutableSubstitution(x, t);
    assertTrue(Matcher.extendMatch(x, t, gamma) == null);
    assertTrue(gamma.get(x) == t);
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testMatchKnownVarWithConflictingMapping() {
    Variable x = TermFactory.createVar("x", type("a"));
    Term t = unaryTerm("f", TermFactory.createConstant("u", type("b")), "a");
    Term q = unaryTerm("f", TermFactory.createConstant("v", type("b")), "a");
    MutableSubstitution gamma = new MutableSubstitution(x, q);
    assertTrue(Matcher.extendMatch(x, t, gamma).toString().equals(
      "Variable x is mapped both to f(v) and to f(u)."));
    assertTrue(gamma.get(x) == q);
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testVarWithBadType() {
    Variable x = TermFactory.createBinder("x", type("a"));
    Term t = unaryTerm("f", TermFactory.createConstant("u", type("b")), "b");
    MutableSubstitution gamma = new MutableSubstitution();
    assertTrue(Matcher.extendMatch(x, t, gamma).toString().equals(
      "Variable x has a different type from f(u)."));
  }

/*
  @Test
  public void testNonPatternDueToNonVariableArg() {
    // F⟨a⟩ matched against a
    MetaVariable f = TermFactory.createMetaVar("F", arrowType("o", "o"), 1);
    Term a = constantTerm("a", type("o"));
    Term t = TermFactory.createMeta(f, a);
    Substitution subst = new MutableSubstitution();
    assertThrows(PatternRequiredException.class, () -> t.match(a, subst));
  }

  @Test
  public void testNonPatternDueToVarArg() {
    // F⟨X⟩ matched against a
    Variable x = TermFactory.createVar("X", type("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType("o", "o"), 1);
    Term t = TermFactory.createMeta(f, x);
    Term a = constantTerm("a", type("o"));
    assertThrows(PatternRequiredException.class, () -> t.match(a, new MutableSubstitution()));
  }

  @Test
  public void testNonPatternDueToSubstitutedVarArg() {
    // F⟨X⟩ matched against a, with X:=y
    Variable x = TermFactory.createVar("X", type("o"));
    Variable y = new Binder("y", type("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType("o", "o"), 1);
    Term t = TermFactory.createMeta(f, x);
    Term a = constantTerm("a", type("o"));
    Substitution subst = new MutableSubstitution();
    subst.extend(x, y);
    assertThrows(PatternRequiredException.class, () -> t.match(a, subst));
  }

  private Term createTwoArgMeta(Term arg1, Term arg2) {
    Type type = arrowType(arg1.queryType(), arrowType(arg2.queryType(), type("o")));
    MetaVariable f = TermFactory.createMetaVar("F", type, 2);
    return TermFactory.createMeta(f, arg1, arg2);
  }

  @Test
  public void testNonPatternDueToBinderNotSubstituted() {
    // F⟨x,y⟩ matched against a where x:=z, but y is not substituted
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Variable z = new Binder("Z", type("o"));
    Term t = createTwoArgMeta(x, y);
    Substitution subst = new MutableSubstitution();
    subst.extend(x, z);
    assertThrows(PatternRequiredException.class, () ->
      t.match(constantTerm("a", type("o")), subst));
  }

  @Test
  public void testNonPatternDueToBinderArgSubstitutedToVar() {
    // F⟨x,y⟩ matched against a where x:=Z,y:=y
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Variable z = TermFactory.createVar("Z", type("o"));
    Term t = createTwoArgMeta(x, y);
    Substitution subst = new MutableSubstitution();
    subst.extend(x, z);
    subst.extend(y, z);
    assertThrows(PatternRequiredException.class, () ->
      t.match(constantTerm("a", type("o")), subst));
  }

  @Test
  public void testNonPatternDueToDuplicateBinder() {
    // F⟨x,x⟩ matched against x
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Term t = createTwoArgMeta(x, x);
    assertThrows(PatternRequiredException.class, () -> t.match(x, new MutableSubstitution()));
  }

  @Test
  public void testNonPatternDueToNonDistinctSubstitutedArgs() {
    // F⟨x,y⟩ matched against a where x:=z and y:=z
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Variable z = new Binder("z", type("o"));
    Term t = createTwoArgMeta(x, y);
    Substitution subst = new MutableSubstitution();
    subst.extend(x, z);
    subst.extend(y, z);
    assertThrows(PatternRequiredException.class, () ->
      t.match(constantTerm("a", type("o")), subst));
  }
  @Test
  public void testProperMatching() {
    // F⟨x,y⟩ matched against h(y, x)
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Variable z = new Binder("z", type("o"));
    Term t = createTwoArgMeta(x, y);
    Substitution subst = new MutableSubstitution();
    subst.extend(x, x);
    subst.extend(y, y);
    Term result =
      TermFactory.createApp(constantTerm("h", arrowType(type("o"), arrowType("o", "o"))), y, x);
    assertTrue(t.match(result, subst) == null);
    assertTrue(subst.get(x) == x);
    assertTrue(subst.get(y) == y);
    assertTrue(subst.get(t.queryMetaVariable()).toString().equals("λx.λy.h(y, x)"));
  }

  @Test
  public void testProperMatchingWithSwitchedVariables() {
    // F⟨x,y⟩ matched against h(y, x) where x:=y and y:=x
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Variable z = new Binder("z", type("o"));
    Term t = createTwoArgMeta(x, y);
    Substitution subst = new MutableSubstitution();
    subst.extend(x, y);
    subst.extend(y, x);
    Term result =
      TermFactory.createApp(constantTerm("h", arrowType(type("o"), arrowType("o", "o"))), y, x);
    assertTrue(t.match(result, subst) == null);
    assertTrue(subst.get(t.queryMetaVariable()).toString().equals("λy.λx.h(y, x)"));
  }

  @Test
  public void testLateAssignmentToArgument() {
    // g(F⟨x⟩, x) against g(x, y)
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("x", type("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType("o", "o"), 1);
    Term g = constantTerm("g", arrowType(type("o"), arrowType("o", "o")));
    Term term = new Application(g, TermFactory.createMeta(f, x), x);

    Term m = new Application(g, x, y);
    Substitution subst = new MutableSubstitution();
    assertTrue(term.match(m, subst) == null);
    assertTrue(subst.get(x) == y);
    assertTrue(subst.get(f).equals(new Abstraction(y, x)));
  }

  @Test
  public void testTooLateAssignmentToArgument() {
    // g(x, F⟨x⟩) against g(y, x)
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("x", type("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType("o", "o"), 1);
    Term g = constantTerm("g", arrowType(type("o"), arrowType("o", "o")));
    Term term = new Application(g, x, TermFactory.createMeta(f, x));

    Term m = new Application(g, y, x);
    Substitution subst = new MutableSubstitution();
    assertThrows(PatternRequiredException.class, () -> term.match(m, subst));
  }

  @Test
  public void testMatchingFailsExistingMapping() {
    // F⟨x,y⟩ against g(x,y) where F is mapped to λxy.g(y,x)
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType(type("o"),arrowType("o","o")), 2);
    Term term = TermFactory.createMeta(f, x, y);
    Term g = constantTerm("g", arrowType(type("o"), arrowType("o", "o")));
    Term m = new Application(g, x, y);
    Substitution subst = new MutableSubstitution();
    subst.extend(x, x);
    subst.extend(y, y);
    subst.extend(f, new Abstraction(x, new Abstraction(y, new Application(g, y, x))));
    assertTrue(term.match(m, subst).equals(
      "Meta-variable F is mapped to both λx.λy.g(y, x) and to λx.λy.g(x, y)."));
  }

  @Test
  public void testMatchingCorrespondsExactlyToExistingMapping() {
    // F⟨x,y⟩ against g(x,y) where F is mapped to λxy.g(x,y)
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType(type("o"),arrowType("o","o")), 2);
    Term term = TermFactory.createMeta(f, x, y);
    Term g = constantTerm("g", arrowType(type("o"), arrowType("o", "o")));
    Term m = new Application(g, x, y);
    Substitution subst = new MutableSubstitution();
    subst.extend(x, x);
    subst.extend(y, y);
    subst.extend(f, new Abstraction(x, new Abstraction(y, new Application(g, x, y))));
    assertTrue(term.match(m, subst) == null);
  }

  @Test
  public void testMatchingAlphaCorrespondsToExistingMapping() {
  // F⟨x,y⟩ against g(u,h(v)) where x:=v,y:=u,F:=λab.g(b,h(a))
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Variable u = new Binder("u", type("o"));
    Variable v = new Binder("v", type("o"));
    Variable a = new Binder("a", type("o"));
    Variable b = new Binder("b", type("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType(type("o"),arrowType("o","o")), 2);
    Term term = TermFactory.createMeta(f, x, y);
    Term g = constantTerm("g", arrowType(type("o"), arrowType("o", "o")));
    Term h = constantTerm("h", arrowType("o", "o"));
    Term m = new Application(g, u, h.apply(v));
    Substitution subst = new MutableSubstitution();
    subst.extend(x, v);
    subst.extend(y, u);
    subst.extend(f, new Abstraction(a, new Abstraction(b, new Application(g, b, h.apply(a)))));
    assertTrue(term.match(m, subst) == null);
  }

  @Test
  public void testNonLinearMetaOccurrence() {
    // λx.λy.g(F⟨x⟩, F⟨y⟩) against λa.λb.g(h(z,a), h(z,b))
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Variable z = new Binder("z", type("o"));
    Variable a = new Binder("a", type("o"));
    Variable b = new Binder("b", type("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType("o", "o"), 1);
    Term g = constantTerm("g", arrowType(type("o"), arrowType("o", "o")));
    Term h = constantTerm("h", arrowType(type("o"), arrowType("o", "o")));
    Term term = new Abstraction(x, new Abstraction(y, new Application(g, TermFactory.createMeta(f, x),
      TermFactory.createMeta(f, y))));
    Term m = new Abstraction(a, new Abstraction(b, new Application(g, new Application(h, z, a),
      new Application(h, z, b))));
    Substitution subst = term.match(m);
    assertTrue(subst.get(f).equals(new Abstraction(x, new Application(h, z, x))));
  }

  @Test
  public void testNonMatchDueToNonLinearity() {
    // λx.g(F⟨x⟩, F⟨x⟩) against λy.g(h(z,y), h(y,z))
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Variable z = new Binder("z", type("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType("o", "o"), 1);
    Term g = constantTerm("g", arrowType(type("o"), arrowType("o", "o")));
    Term h = constantTerm("h", arrowType(type("o"), arrowType("o", "o")));
    Term fx = TermFactory.createMeta(f, x);
    Term term = new Abstraction(x, new Application(g, fx, fx));
    Term m = new Abstraction(y, new Application(g, new Application(h,z,y), new Application(h,y,z)));
    assertTrue(term.match(m, new MutableSubstitution()) != null);
  }

  @Test
  public void testFirstOrderMatching() {
    Type ii = type("Int");
    Variable x = TermFactory.createVar("x", ii);
    Variable y = TermFactory.createVar("y", ii);
    Variable z = new Binder("z", ii);
    Type ty = arrowType(ii, arrowType(ii, ii));
    FunctionSymbol plus = new Constant("plus", ty);
    FunctionSymbol f = new Constant("f", ty);

    Term pattern1 = new Application(f, x, new Application(plus, y, z));
    Term pattern2 = new Application(f, x, new Application(plus, y, x));
    Term pattern3 = new Application(f, x, new Application(plus, y, y));
    Term pattern4 = new Application(plus, x, new Application(f, y, z));

    Term a = new Application(f, constantTerm("37", ii), z);
    Term combi = new Application(f, a, new Application(plus, y, a));

    Substitution subst1 = new MutableSubstitution();
    Substitution subst2 = new MutableSubstitution();
    Substitution subst3 = new MutableSubstitution();
    Substitution subst4 = new MutableSubstitution();

    assertTrue(pattern1.match(combi, subst1) == null);
    assertTrue(pattern2.match(combi, subst2) == null);
    assertTrue(pattern3.match(combi, subst3) != null);
    assertTrue(pattern4.match(combi, subst4) != null);

    assertTrue(subst1.domain().size() == 3);
    assertTrue(subst1.get(x).equals(a));
    assertTrue(subst1.get(y).equals(y));
    assertTrue(subst1.get(z).equals(a));

    assertTrue(subst2.domain().size() == 2);
    assertTrue(subst2.get(x).equals(a));
    assertTrue(subst2.get(y).equals(y));
  }

  @Test
  public void testBasicVarTermMatching() {
    Variable x = new Binder("x", type("Int"));
    Variable z = new Binder("Z", arrowType(type("Int"), arrowType("Int", "Int")));
    Term three = constantTerm("3", type("Int"));
    Term four = constantTerm("4", type("Int"));
    Type intintint = arrowType(type("Int"), arrowType("Int", "Int"));
    FunctionSymbol g = new Constant("g", intintint);
    FunctionSymbol h = new Constant("h", arrowType(type("Int"), intintint));
    Term pattern = new Application(z, three, x);
    Term fx = unaryTerm("f", type("Int"), x);
    List<Term> args = new ArrayList<Term>();
    args.add(fx);
    args.add(three);
    args.add(fx);
    Term s = new Application(h, args);
    Term t = new Application(g, four, three);

    // Z(3, x) is asked to match with h(f(x), 3, f(x))
    // This should map Z to h(f(x)) and x to f(x)
    Substitution gamma = pattern.match(s);
    Substitution delta = pattern.match(t);

    assertTrue(gamma != null);
    assertTrue(delta == null);

    assertTrue(gamma.get(x).equals(fx));
    assertTrue(gamma.get(z).equals(new Application(h, fx)));
    assertTrue(gamma.domain().size() == 2);
  }

  @Test
  public void testNonLinearMatching() {
    Variable x = new Binder("x", arrowType("o", "o"));
    Term a = constantTerm("a", type("o"));
    Term b = constantTerm("b", type("o"));
    Type ooo = arrowType(type("o"), arrowType("o", "o"));
    FunctionSymbol f = new Constant("f", ooo);
    FunctionSymbol g = new Constant("g", arrowType("o", "o"));
    FunctionSymbol h = new Constant("h", ooo);
    Term pattern = new Application(f, new Application(x, a), new Application(x, b));
      // f(x(a), x(b))

    Term s = new Application(f, new Application(g, a), new Application(g, b));
    Term t = new Application(f, new Application(h, a, a), new Application(h, a, b));
    Term q = new Application(f, new Application(h, a, a), new Application(h, b, b));
    Term u = new Application(f, a, b);

    Substitution gamma = pattern.match(s);
    assertTrue(gamma != null);
    assertTrue(gamma.get(x).equals(g));

    Substitution delta = pattern.match(t);
    assertTrue(delta != null);
    assertTrue(delta.get(x).equals(new Application(h, a)));

    assertTrue(pattern.match(q) == null);
    assertTrue(pattern.match(u) == null);
  }

  @Test
  public void testOnlySemiPattern() {
    // F⟨x⟩(a, Y) matched against both h(g(x), a, b) and h(g(x), b, a)
    Variable x = new Binder("x", type("o"));
    Variable y = TermFactory.createVar("Y", type("o"));
    Term a = constantTerm("a", type("o"));
    Term b = constantTerm("b", type("o"));
    Term g = constantTerm("g", arrowType("o", "o"));
    Type oooo = arrowType(type("o"), arrowType(type("o"), arrowType("o", "o")));
    Term h = constantTerm("h", oooo);
    MetaVariable f = TermFactory.createMetaVar("F", oooo, 1);
    Term term = new Application(TermFactory.createMeta(f, x), a, y);

    Term m1 = new Application(h.apply(g.apply(x)), a, b);
    Term m2 = new Application(h.apply(g.apply(x)), b, a);

    Substitution subst = new MutableSubstitution();
    subst.extend(x, x);
    assertTrue(term.match(m1, subst) == null);
    assertTrue(subst.get(x) == x);
    assertTrue(subst.get(y) == b);
    assertTrue(subst.get(f).equals(new Abstraction(x, h.apply(g.apply(x)))));

    subst = new MutableSubstitution();
    subst.extend(x, x);
    assertTrue(term.match(m2, subst) != null);
  }

  @Test
  public void testSuccessfulMatchFreeBecomesBound() {
    // λx.f(x, y)
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Constant f = new Constant("f", arrowType(type("o"), arrowType("o", "o")));
    Term term = new Abstraction(x, new Application(f, x, y));

    // λy.f(y, g(a))
    Term a = new Constant("a", type("o"));
    Term g = new Constant("g", arrowType("o", "o"));
    Term m = new Abstraction(y, new Application(f, y, g.apply(a)));

    Substitution gamma = new MutableSubstitution();
    assertNull(term.match(m, gamma));
    assertNull(gamma.get(x));
    assertTrue(gamma.get(y).equals(g.apply(a)));
  }

  @Test
  public void testSuccessfulMatchSameBinder() {
    // λx.f(x, f(x, y))
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Constant f = new Constant("f", arrowType(type("o"), arrowType("o", "o")));
    Term term = new Abstraction(x, new Application(f, x, new Application(f, x, y)));

    // λx.f(x, f(x, a))
    Term a = new Constant("a", type("o"));
    Term m = new Abstraction(x, new Application(f, x, new Application(f, x, a)));

    Substitution gamma = new MutableSubstitution();
    assertTrue(term.match(m, gamma) == null);
    assertTrue(gamma.get(x) == null);
    assertTrue(gamma.get(y).equals(a));
  }

  public void testMatchSwitchVariables() {
    // λy.λx.f(x, z(y))
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Variable z = TermFactory.createVar("z", arrowType("o", "o"));
    Constant f = new Constant("f", arrowType(type("o"), arrowType("o", "o")));
    Term term = new Abstraction(y, new Abstraction(x, new Application(f, z.apply(y))));

    // λx.λy.f(y, f(a, x))
    Term a = new Constant("a", type("o"));
    Term m = new Abstraction(x, new Abstraction(y, new Application(f,
      new Application(f, a, x))));

    Substitution gamma = new MutableSubstitution();
    assertTrue(term.match(m, gamma) == null);
    assertTrue(gamma.get(x) == null);
    assertTrue(gamma.get(y) == null);
    assertTrue(gamma.get(z).equals(f.apply(a)));
  }

  @Test
  public void testMatchNonAbstractionFails() {
    // λx.f(x, y)
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Constant f = new Constant("f", arrowType(type("o"), arrowType("o", "o")));
    Term term = new Abstraction(x, new Application(f, x, y));

    // Z
    Term z = TermFactory.createVar("Z", arrowType("o", "o"));

    Substitution gamma = new MutableSubstitution();
    assertTrue(term.match(z, gamma) != null);
  }

  @Test
  public void testDoNotInstantiateBinder() {
    // λx.x
    Variable x = new Binder("x", type("o"));
    Term term = new Abstraction(x, x);

    // λx.y
    Variable y = new Binder("y", type("o"));
    Term m = new Abstraction(x, y);

    Substitution gamma = new MutableSubstitution();
    assertTrue(term.match(m, gamma) != null);
  }

  @Test
  public void testDoNotInstantiateWithBinder() {
    // λx.y
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Term term = new Abstraction(x, y);

    // λx.x
    Term m = new Abstraction(x, x);

    Substitution gamma = new MutableSubstitution();
    assertTrue(term.match(m, gamma) != null);
  }

  @Test
  public void testMatchBinderVariableMayNotOccurDeeperInRange() {
    // λx.f(x, y)
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Constant f = new Constant("f", arrowType(type("o"), arrowType("o", "o")));
    Term term = new Abstraction(x, new Application(f, x, y));

    // λz.f(z, g(z))
    Variable z = new Binder("z", type("o"));
    Constant g = new Constant("g", arrowType("o", "o"));
    Term m = new Abstraction(z, new Application(f, z, new Application(g, z)));

    Substitution gamma = new MutableSubstitution();
    assertTrue(term.match(m, gamma) != null);
  }

  @Test
  public void testMatchWithMetaApplication() {
    // λx.g(F⟨z,x⟩)
    Variable x = new Binder("x", type("o"));
    Variable z = new Binder("z", type("o"));
    MetaVariable f =
      TermFactory.createMetaVar("F", arrowType(type("o"), arrowType("o", "o")), 2);
    Term g = constantTerm("g", arrowType("o", "o"));
    Term term = new Abstraction(x, g.apply(TermFactory.createMeta(f, z, x)));

    // λy.g(h(a(y), z))
    Variable y = new Binder("y", type("o"));
    Term a = constantTerm("a", arrowType("o", "o"));
    Term h = constantTerm("h", arrowType(type("o"), arrowType("o", "o")));
    Term m = new Abstraction(y, g.apply(new Application(h, a.apply(y), z)));

    Substitution gamma = new MutableSubstitution();
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
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    MetaVariable f = TermFactory.createMetaVar("Z", arrowType("o", "o"), 1);
    Term term = new Abstraction(x, new Abstraction(y, TermFactory.createMeta(f, x)));

    // λx.λy.h(x, z)
    Variable z = new Binder("z", type("o"));
    Term h = constantTerm("h", arrowType(type("o"), arrowType("o", "o")));
    Term m1 = new Abstraction(x, new Abstraction(y, new Application(h, x, z)));
    // λx.λy.h(x, y)
    Term m2 = new Abstraction(x, new Abstraction(y, new Application(h, x, y)));

    assertNull(term.match(m1, new MutableSubstitution()));
    assertNotNull(term.match(m2, new MutableSubstitution()));
  }

  @Test
  public void testMatch() {
    Variable x = TermFactory.createVar("X", type("A"));
    Variable y = TermFactory.createVar("Y", type("A"));
    Term tuple = new Tuple(x, y, x);

    Term a = constantTerm("a", type("A"));
    Term b = constantTerm("b", type("A"));
    Term c = constantTerm("c", type("A"));
    Substitution gamma;
    Term m;

    gamma = new MutableSubstitution();
    assertTrue(tuple.match(a, gamma).equals(
      "a does not instantiate ⦇X, Y, X⦈ (not a tuple term)."));

    m = new Tuple(a, new Tuple(b, a));
    gamma = new MutableSubstitution();
    assertTrue(tuple.match(m, gamma).equals(
      "⦇a, ⦇b, a⦈⦈ does not instantiate ⦇X, Y, X⦈ (mismatch on the tuple sizes)."));

    m = new Tuple(a, b, c);
    gamma = new MutableSubstitution();
    assertTrue(tuple.match(m, gamma).equals("Variable X mapped both to a and to c."));

    m = new Tuple(a, b, a);
    gamma = new MutableSubstitution();
    assertTrue(tuple.match(m, gamma) == null);
    assertTrue(gamma.get(x) == a);
    assertTrue(gamma.get(y) == b);
  }
*/
}

