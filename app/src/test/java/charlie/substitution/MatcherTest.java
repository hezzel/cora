/**************************************************************************************************
 Copyright 2019--2026 Cynthia Kop

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
import charlie.types.*;
import charlie.parser.CoraParser;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.*;
import charlie.theory.TheoryFactory;

public class MatcherTest {
  private Type type(String str) {
    return CoraParser.readType(str);
  }

  private Term unaryTerm(String symbol, Term arg, String outtype) {
    Term f =
      TermFactory.createConstant(symbol, TypeFactory.createArrow(arg.queryType(), type(outtype)));
    return f.apply(arg);
  }

  private Term createTwoArgMeta(Term arg1, Term arg2) {
    Type type = TypeFactory.createArrow(arg1.queryType(),
                  TypeFactory.createArrow(arg2.queryType(), type("o")));
    MetaVariable f = TermFactory.createMetaVar("F", type, 2);
    return TermFactory.createMeta(f, arg1, arg2);
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

  @Test
  public void testFirstOrderMatching() {
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Variable z = TermFactory.createBinder("z", type("Int"));
    FunctionSymbol plus = TermFactory.createConstant("plus", type("Int -> Int -> Int"));
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int -> Int"));

    Term pattern1 = TermFactory.createApp(f, x, TermFactory.createApp(plus, y, z));
    Term pattern2 = TermFactory.createApp(f, x, TermFactory.createApp(plus, y, x));
    Term pattern3 = TermFactory.createApp(f, x, TermFactory.createApp(plus, y, y));
    Term pattern4 = TermFactory.createApp(plus, x, TermFactory.createApp(f, y, z));

    Term a = TermFactory.createApp(f, TermFactory.createConstant("37", type("Int")), z);
    Term combi = TermFactory.createApp(f, a, TermFactory.createApp(plus, y, a));
      // f(f(37, z), plus(y, f(37, z)))

    Substitution subst1 = Matcher.match(pattern1, combi);
    Substitution subst2 = Matcher.match(pattern2, combi);
    assertTrue(Matcher.match(pattern3, combi) == null);
    assertTrue(Matcher.match(pattern4, combi) == null);

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
    Variable x = TermFactory.createBinder("x", type("Int"));
    Variable z = TermFactory.createBinder("Z", type("Int -> Int -> Int"));
    Term three = TermFactory.createConstant("3", type("Int"));
    Term four = TermFactory.createConstant("4", type("Int"));
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> Int -> Int"));
    FunctionSymbol h = TermFactory.createConstant("h", type("Int -> Int -> Int -> Int"));
    Term pattern = TermFactory.createApp(z, three, x);
    Term fx = unaryTerm("f", x, "Int");
    Term s = TermFactory.createApp(h, List.of(fx, three, fx));
    Term t = TermFactory.createApp(g, four, three);

    // Z(3, x) is asked to match with h(f(x), 3, f(x))
    // This should map Z to h(f(x)) and x to f(x)
    Substitution gamma = Matcher.match(pattern, s);
    Substitution delta = Matcher.match(pattern, t);

    assertTrue(gamma != null);
    assertTrue(delta == null);

    assertTrue(gamma.get(x).equals(fx));
    assertTrue(gamma.get(z).equals(TermFactory.createApp(h, fx)));
    assertTrue(gamma.domain().size() == 2);
  }

  @Test
  public void testNonLinearApplicationMatching() {
    Variable x = TermFactory.createBinder("x", type("o -> o"));
    Term a = TermFactory.createConstant("a", type("o"));
    Term b = TermFactory.createConstant("b", type("o"));
    FunctionSymbol f = TermFactory.createConstant("f", type("o -> o -> o"));
    FunctionSymbol g = TermFactory.createConstant("g", type("o -> o"));
    FunctionSymbol h = TermFactory.createConstant("h", type("o -> o -> o"));
    Term pattern = // f(x(a), x(b))
      TermFactory.createApp(f, TermFactory.createApp(x, a), TermFactory.createApp(x, b));

    Term s = TermFactory.createApp(f, TermFactory.createApp(g,a), TermFactory.createApp(g,b));
    Term t = TermFactory.createApp(f, TermFactory.createApp(h,a,a), TermFactory.createApp(h,a,b));
    Term q = TermFactory.createApp(f, TermFactory.createApp(h,a,a), TermFactory.createApp(h,b,b));
    Term u = TermFactory.createApp(f, a, b);

    Substitution gamma = Matcher.match(pattern, s);
    assertTrue(gamma != null);
    assertTrue(gamma.get(x).equals(g));

    Substitution delta = Matcher.match(pattern, t);
    assertTrue(delta != null);
    assertTrue(delta.get(x).equals(TermFactory.createApp(h, a)));

    assertTrue(Matcher.match(pattern, q) == null);
    assertTrue(Matcher.match(pattern, u) == null);
  }

  @Test
  public void testNonPatternDueToNonVariableArg() {
    // F⟨a⟩ matched against a
    MetaVariable f = TermFactory.createMetaVar("F", type("o -> o"), 1);
    Term a = TermFactory.createConstant("a", type("o"));
    Term t = TermFactory.createMeta(f, a);
    assertThrows(PatternRequiredException.class, () -> Matcher.match(t, a));
  }

  @Test
  public void testNonPatternDueToVarArg() {
    // F⟨X⟩ matched against a
    Variable x = TermFactory.createVar("X", type("o"));
    MetaVariable f = TermFactory.createMetaVar("F", type("o -> o"), 1);
    Term t = TermFactory.createMeta(f, x);
    Term a = TermFactory.createConstant("a", type("o"));
    assertThrows(PatternRequiredException.class, () -> Matcher.match(t, a));
  }

  @Test
  public void testNonPatternDueToSubstitutedVarArg() {
    // F⟨X⟩ matched against a, with X:=y
    Variable x = TermFactory.createVar("X", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    MetaVariable f = TermFactory.createMetaVar("F", type("o -> o"), 1);
    Term t = TermFactory.createMeta(f, x);
    Term a = TermFactory.createConstant("a", type("o"));
    MutableSubstitution subst = new MutableSubstitution(x, y);
    assertThrows(PatternRequiredException.class, () -> Matcher.extendMatch(t, a, subst));
  }

  @Test
  public void testNonPatternDueToBinderNotSubstituted() {
    // F⟨x,y⟩ matched against a where x:=z, but y is not substituted
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Variable z = TermFactory.createBinder("Z", type("o"));
    Term t = createTwoArgMeta(x, y);
    MutableSubstitution subst = new MutableSubstitution(x, z);
    assertThrows(PatternRequiredException.class, () ->
      Matcher.extendMatch(t, TermFactory.createConstant("a", type("o")), subst));
  }

  @Test
  public void testNonPatternDueToBinderArgSubstitutedToVar() {
    // F⟨x,y⟩ matched against a where x:=Z,y:=y
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Variable z = TermFactory.createVar("Z", type("o"));
    Term t = createTwoArgMeta(x, y);
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(x, z);
    subst.extend(y, y);
    assertThrows(PatternRequiredException.class, () ->
      Matcher.extendMatch(t, TermFactory.createConstant("a", type("o")), subst));
  }

  @Test
  public void testNonPatternDueToDuplicateBinder() {
    // F⟨x,x⟩ matched against y
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    MutableSubstitution subst = new MutableSubstitution(x, y);
    Term t = createTwoArgMeta(x, x);
    assertThrows(PatternRequiredException.class, () -> Matcher.extendMatch(t, y, subst));
  }

  @Test
  public void testNonPatternDueToNonDistinctSubstitutedArgs() {
    // F⟨x,y⟩ matched against a where x:=z and y:=z
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Variable z = TermFactory.createBinder("z", type("o"));
    Term t = createTwoArgMeta(x, y);
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(x, z);
    subst.extend(y, z);
    assertThrows(PatternRequiredException.class, () ->
      Matcher.extendMatch(t, TermFactory.createConstant("a", type("o")), subst));
  }

  @Test
  public void testProperMetaMatching() {
    // F⟨x,y⟩ matched against h(y, x)
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Term t = createTwoArgMeta(x, y);
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(x, x);
    subst.extend(y, y);
    Term h = TermFactory.createConstant("h", type("o -> o -> o"));
    Term result = TermFactory.createApp(h, y, x);
    assertTrue(Matcher.extendMatch(t, result, subst) == null);
    assertTrue(subst.get(x) == x);
    assertTrue(subst.get(y) == y);
    assertTrue(subst.get(t.queryMetaVariable()).toString().equals("λx.λy.h(y, x)"));
  }

  @Test
  public void testProperMatchingWithSwitchedVariables() {
    // F⟨x,y⟩ matched against h(y, x) where x:=y and y:=x
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Variable z = TermFactory.createBinder("z", type("o"));
    Term t = createTwoArgMeta(x, y);
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(x, y);
    subst.extend(y, x);
    Term result = TermFactory.createApp(TermFactory.createConstant("h", type("o -> o -> o")), y, x);
    assertTrue(Matcher.extendMatch(t, result, subst) == null);
    assertTrue(subst.get(t.queryMetaVariable()).toString().equals("λy.λx.h(y, x)"));
  }

  @Test
  public void testLateAssignmentToApplicationArgument() {
    // g(F⟨x⟩, x) against g(x, y)
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("x", type("o"));
    MetaVariable f = TermFactory.createMetaVar("F", type("o -> o"), 1);
    Term g = TermFactory.createConstant("g", type("o -> o -> o"));
    Term term = TermFactory.createApp(g, TermFactory.createMeta(f, x), x);

    Term m = TermFactory.createApp(g, x, y);
    MutableSubstitution subst = Matcher.match(term, m);
    assertTrue(subst.get(x) == y);
    assertTrue(subst.get(f).equals(TermFactory.createAbstraction(y, x)));
  }

  @Test
  public void testTooLateAssignmentToApplicationArgument() {
    // g(x, F⟨x⟩) against g(y, x)
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("x", type("o"));
    MetaVariable f = TermFactory.createMetaVar("F", type("o -> o"), 1);
    Term g = TermFactory.createConstant("g", type("o -> o -> o"));
    Term term = TermFactory.createApp(g, x, TermFactory.createMeta(f, x));

    Term m = TermFactory.createApp(g, y, x);
    assertThrows(PatternRequiredException.class, () -> Matcher.match(term, m));
  }

  @Test
  public void testMatchingFailsExistingMapping() {
    // F⟨x,y⟩ against g(x,y) where F is mapped to λxy.g(y,x)
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Term term = createTwoArgMeta(x, y);
    Term g = TermFactory.createConstant("g", type("o -> o -> o"));
    Term m = TermFactory.createApp(g, x, y);
    MutableSubstitution subst = new MutableSubstitution(x, x);
    subst.extend(y, y);
    subst.extend(term.queryMetaVariable(), TermFactory.createAbstraction(x,
      TermFactory.createAbstraction(y, TermFactory.createApp(g, y, x))));
    assertTrue(Matcher.extendMatch(term, m, subst).toString().equals(
      "Meta-variable F is mapped to both λx.λy.g(y, x) and to λx.λy.g(x, y)."));
  }

  @Test
  public void testMatchingCorrespondsExactlyToExistingMapping() {
    // F⟨x,y⟩ against g(x,y) where F is mapped to λxy.g(x,y)
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Term term = createTwoArgMeta(x, y);
    Term g = TermFactory.createConstant("g", type("o -> o -> o"));
    Term m = TermFactory.createApp(g, x, y);
    MutableSubstitution subst = new MutableSubstitution(x, x);
    subst.extend(y, y);
    subst.extend(term.queryMetaVariable(), TermFactory.createAbstraction(x,
      TermFactory.createAbstraction(y, TermFactory.createApp(g, x, y))));
    assertTrue(Matcher.extendMatch(term, m, subst) == null);
  }

  @Test
  public void testMatchingAlphaCorrespondsToExistingMapping() {
    // F⟨x,y⟩ against g(u,h(v)) where x:=v,y:=u,F:=λab.g(b,h(a))
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Variable u = TermFactory.createBinder("u", type("o"));
    Variable v = TermFactory.createBinder("v", type("o"));
    Variable a = TermFactory.createBinder("a", type("o"));
    Variable b = TermFactory.createBinder("b", type("o"));
    Term term = createTwoArgMeta(x, y);
    Term g = TermFactory.createConstant("g", type("o -> o -> o"));
    Term h = TermFactory.createConstant("h", type("o -> o"));
    Term m = TermFactory.createApp(g, u, h.apply(v));
    MutableSubstitution subst = new MutableSubstitution(x, v);
    subst.extend(y, u);
    subst.extend(term.queryMetaVariable(), TermFactory.createAbstraction(a,
      TermFactory.createAbstraction(b, TermFactory.createApp(g, b, h.apply(a)))));
    assertTrue(Matcher.extendMatch(term, m, subst) == null);
  }

  @Test
  public void testTypeFail() {
    Variable x = TermFactory.createBinder("x", type("A"));
    Variable y = TermFactory.createBinder("y", type("B"));
    Term sub = TermFactory.createConstant("c", type("C"));
    Term original = TermFactory.createAbstraction(x, sub);
    Term instance = TermFactory.createAbstraction(y, sub);
    MutableSubstitution subst = new MutableSubstitution();
    assertTrue(Matcher.extendMatch(original, instance, subst).toString().equals(
      "Abstraction λx.c is not instantiated by λy.c because the types of the abstraction " +
      "variables do not match (A versus B)."));
  }

  @Test
  public void testNonLinearMetaOccurrence() {
    // λx.λy.g(F⟨x⟩, F⟨y⟩) against λa.λb.g(h(z,a), h(z,b))
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Variable z = TermFactory.createBinder("z", type("o"));
    Variable a = TermFactory.createBinder("a", type("o"));
    Variable b = TermFactory.createBinder("b", type("o"));
    MetaVariable f = TermFactory.createMetaVar("F", type("o -> o"), 1);
    Term g = TermFactory.createConstant("g", type("o -> o -> o"));
    Term h = TermFactory.createConstant("h", type("o -> o -> o"));
    Term term = TermFactory.createAbstraction(x, TermFactory.createAbstraction(y,
      TermFactory.createApp(g, TermFactory.createMeta(f, x), TermFactory.createMeta(f, y))));
    Term m = TermFactory.createAbstraction(a, TermFactory.createAbstraction(b,
      TermFactory.createApp(g, TermFactory.createApp(h, z, a), TermFactory.createApp(h, z, b))));
    Substitution subst = Matcher.match(term, m);
    assertTrue(subst.get(f).equals(
      TermFactory.createAbstraction(x, TermFactory.createApp(h, z, x))));
  }

  @Test
  public void testNonMatchDueToNonLinearity() {
    // λx.g(F⟨x⟩, F⟨x⟩) against λy.g(h(z,y), h(y,z))
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Variable z = TermFactory.createBinder("z", type("o"));
    MetaVariable f = TermFactory.createMetaVar("F", type("o -> o"), 1);
    Term g = TermFactory.createConstant("g", type("o -> o -> o"));
    Term h = TermFactory.createConstant("h", type("o -> o -> o"));
    Term fx = TermFactory.createMeta(f, x);
    Term term = TermFactory.createAbstraction(x, TermFactory.createApp(g, fx, fx));
    Term m = TermFactory.createAbstraction(y, TermFactory.createApp(g,
      TermFactory.createApp(h,z,y), TermFactory.createApp(h,y,z)));
    String s = Matcher.extendMatch(term, m, new MutableSubstitution()).toString();
    assertTrue(s.equals("Meta-variable F is mapped to both λy.h(y, z) and to λy.h(z, y)."));
  }

  @Test
  public void testOnlySemiPattern() {
    // F⟨x⟩(a, Y) matched against both h(g(x), a, b) and h(g(x), b, a)
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createVar("Y", type("o"));
    Term a = TermFactory.createConstant("a", type("o"));
    Term b = TermFactory.createConstant("b", type("o"));
    Term g = TermFactory.createConstant("g", type("o -> o"));
    Type oooo = type("o -> o -> o -> o");
    Term h = TermFactory.createConstant("h", oooo);
    MetaVariable f = TermFactory.createMetaVar("F", oooo, 1);
    Term term = TermFactory.createApp(TermFactory.createMeta(f, x), a, y);

    Term m1 = TermFactory.createApp(h.apply(g.apply(x)), a, b);
    Term m2 = TermFactory.createApp(h.apply(g.apply(x)), b, a);

    MutableSubstitution subst = new MutableSubstitution(x, x);
    assertTrue(Matcher.extendMatch(term, m1, subst) == null);
    assertTrue(subst.get(x) == x);
    assertTrue(subst.get(y) == b);
    assertTrue(subst.get(f).equals(TermFactory.createAbstraction(x, h.apply(g.apply(x)))));

    subst = new MutableSubstitution(x, x);
    assertTrue(Matcher.extendMatch(term, m2, subst) != null);
  }

  @Test
  public void testSuccessfulMatchFreeBecomesBound() {
    // λx.f(x, y)
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Term f = TermFactory.createConstant("f", type("o -> o -> o"));
    Term term = TermFactory.createAbstraction(x, TermFactory.createApp(f, x, y));

    // λy.f(y, g(a))
    Term a = TermFactory.createConstant("a", type("o"));
    Term g = TermFactory.createConstant("g", type("o -> o"));
    Term m = TermFactory.createAbstraction(y, TermFactory.createApp(f, y, g.apply(a)));

    MutableSubstitution gamma = new MutableSubstitution();
    assertNull(Matcher.extendMatch(term, m, gamma));
    assertNull(gamma.get(x));
    assertTrue(gamma.get(y).equals(g.apply(a)));
  }

  @Test
  public void testSuccessfulMatchSameBinder() {
    // λx.f(x, f(x, y))
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Term f = TermFactory.createConstant("f", type("o -> o -> o"));
    Term term = TermFactory.createAbstraction(x,
      TermFactory.createApp(f, x, TermFactory.createApp(f, x, y)));

    // λx.f(x, f(x, a))
    Term a = TermFactory.createConstant("a", type("o"));
    Term m = TermFactory.createAbstraction(x,
      TermFactory.createApp(f, x, TermFactory.createApp(f, x, a)));

    Substitution gamma = Matcher.match(term, m);
    assertTrue(gamma != null);
    assertTrue(gamma.get(x) == null);
    assertTrue(gamma.get(y).equals(a));
  }

  public void testMatchSwitchVariables() {
    // λy.λx.f(x, z(y))
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Variable z = TermFactory.createVar("z", type("o -> o"));
    Term f = TermFactory.createConstant("f", type("o -> o -> o"));
    Term term = TermFactory.createAbstraction(y,
      TermFactory.createAbstraction(x, TermFactory.createApp(f, z.apply(y))));

    // λx.λy.f(y, f(a, x))
    Term a = TermFactory.createConstant("a", type("o"));
    Term m = TermFactory.createAbstraction(x, TermFactory.createAbstraction(y,
      TermFactory.createApp(f, TermFactory.createApp(f, a, x))));

    MutableSubstitution gamma = new MutableSubstitution();
    assertTrue(Matcher.extendMatch(term, m, gamma) == null);
    assertTrue(gamma.get(x) == null);
    assertTrue(gamma.get(y) == null);
    assertTrue(gamma.get(z).equals(f.apply(a)));
  }

  @Test
  public void testMatchNonAbstractionFails() {
    // λx.f(x, y)
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Term f = TermFactory.createConstant("f", type("o -> o -> o"));
    Term term = TermFactory.createAbstraction(x, TermFactory.createApp(f, x, y));

    // Z
    Term z = TermFactory.createVar("Z", type("o -> o"));

    assertTrue(Matcher.match(term, z) == null);
  }

  @Test
  public void testDoNotInstantiateBinder() {
    // λx.x
    Variable x = TermFactory.createBinder("x", type("o"));
    Term term = TermFactory.createAbstraction(x, x);

    // λx.y
    Variable y = TermFactory.createBinder("y", type("o"));
    Term m = TermFactory.createAbstraction(x, y);

    MutableSubstitution gamma = new MutableSubstitution();
    assertTrue(Matcher.extendMatch(term, m, gamma).toString().equals(
      "Binder variable x is mapped both to x and to y."));
  }

  @Test
  public void testDoNotInstantiateWithBinder() {
    // λx.y
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Term term = TermFactory.createAbstraction(x, y);

    // λx.x
    Term m = TermFactory.createAbstraction(x, x);

    MutableSubstitution gamma = new MutableSubstitution();
    assertTrue(Matcher.extendMatch(term, m, gamma).toString().equals(
      "Abstraction λx.y is not instantiated by λx.x because the induced mapping " +
      "[y := x] contains the binder variable of λx.x."));
  }

  @Test
  public void testMatchBinderVariableMayNotOccurDeeperInRange() {
    // λx.f(x, y)
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Term f = TermFactory.createConstant("f", type("o -> o -> o"));
    Term term = TermFactory.createAbstraction(x, TermFactory.createApp(f, x, y));

    // λz.f(z, g(z))
    Variable z = TermFactory.createBinder("z", type("o"));
    Term g = TermFactory.createConstant("g", type("o -> o"));
    Term m =
      TermFactory.createAbstraction(z, TermFactory.createApp(f, z, TermFactory.createApp(g, z)));

    MutableSubstitution gamma = new MutableSubstitution();
    assertTrue(Matcher.extendMatch(term, m, gamma).toString().equals(
      "Abstraction λx.f(x, y) is not instantiated by λz.f(z, g(z)) because the induced mapping " +
      "[y := g(z)] contains the binder variable of λz.f(z, g(z))."));
  }

  @Test
  public void testMatchWithMetaApplication() {
    // λx.g(F⟨z,x⟩)
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable z = TermFactory.createBinder("z", type("o"));
    MetaVariable f = TermFactory.createMetaVar("F", type("o -> o -> o"), 2);
    Term g = TermFactory.createConstant("g", type("o -> o"));
    Term term = TermFactory.createAbstraction(x, g.apply(TermFactory.createMeta(f, z, x)));

    // λy.g(h(a(y), z))
    Variable y = TermFactory.createBinder("y", type("o"));
    Term a = TermFactory.createConstant("a", type("o -> o"));
    Term h = TermFactory.createConstant("h", type("o -> o -> o"));
    Term m = TermFactory.createAbstraction(y, g.apply(TermFactory.createApp(h, a.apply(y), z)));

    MutableSubstitution gamma = new MutableSubstitution(z, z);
    assertNull(Matcher.extendMatch(term, m, gamma));
    assertNull(gamma.get(x));
    assertNull(gamma.get(y));
    assertSame(gamma.get(z), z);
    assertEquals("λz.λy.h(a(y), z)", gamma.get(f).toString());
  }

  @Test
  public void testMatchWithPartialMetaApplication() {
    // λx.λy.F[x]
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    MetaVariable f = TermFactory.createMetaVar("Z", type("o -> o"), 1);
    Term term = TermFactory.createAbstraction(x,
      TermFactory.createAbstraction(y, TermFactory.createMeta(f, x)));

    // λx.λy.h(x, z)
    Variable z = TermFactory.createBinder("z", type("o"));
    Term h = TermFactory.createConstant("h", type("o -> o -> o"));
    Term m1 = TermFactory.createAbstraction(x,
      TermFactory.createAbstraction(y, TermFactory.createApp(h, x, z)));
    // λx.λy.h(x, y)
    Term m2 = TermFactory.createAbstraction(x,
      TermFactory.createAbstraction(y, TermFactory.createApp(h, x, y)));

    assertNotNull(Matcher.match(term, m1));
    assertNull(Matcher.match(term, m2));
  }

  @Test
  public void testPolymorphicConstant() {
    TVar alpha = TypeFactory.createVariable("α");
    TVar beta = TypeFactory.createVariable("β");
    Term s = TermFactory.createConstant("f", type("$α -> $β -> $α"));
    Term a = TermFactory.createConstant("f", type("Int -> (Bool → $α) → Int"));
    Term b = TermFactory.createConstant("f", type("Int -> (Bool → $α) → Bool"));
    Term c = TermFactory.createConstant("g", type("Int -> (Bool → $α) → Int"));

    MutableSubstitution subst = Matcher.match(s, a);
    assertTrue(subst.domain().isEmpty());
    assertTrue(subst.typeDomain().size() == 2);
    assertTrue(subst.get(alpha).equals(type("Int")));
    assertTrue(subst.get(beta).equals(type("Bool → $α")));

    subst = new MutableSubstitution();
    subst.extend(alpha, type("Int"));
    assertTrue(Matcher.extendMatch(s, a, subst) == null);

    subst = new MutableSubstitution();
    subst.extend(beta, type("Int"));
    assertTrue(Matcher.extendMatch(s, a, subst).toString().equals("Constant f (of type " +
      "$α → $β → $α) is not instantiated by symbol f (of type Int → (Bool → $α) → Int)."));

    assertTrue(Matcher.match(s, b) == null);

    subst = new MutableSubstitution();
    assertTrue(Matcher.extendMatch(s, c, subst).toString().equals(
      "Constant f is not instantiated by g."));

    subst = Matcher.match(s, s);
    assertTrue(subst.domain().isEmpty());
    assertTrue(subst.typeDomain().size() == 2);
    assertTrue(subst.get(alpha).equals(alpha));
  }

  @Test
  public void testPolymorphicVariable() {
    TVar alpha = TypeFactory.createVariable("α");
    TVar beta = TypeFactory.createVariable("β");
    Variable x = TermFactory.createVar("x", type("$α -> $β -> $γ"));
    Term f = TermFactory.createConstant("f", type("Int -> (Bool → $α) → Int → Int"));
    Term fa = f.apply(TermFactory.createConstant("a", type("Int")));
    Term fab = fa.apply(TermFactory.createConstant("b", type("Bool -> $α")));

    MutableSubstitution subst = Matcher.match(x, f);
    assertTrue(subst.domain().size() == 1);
    assertTrue(subst.get(x) == f);
    assertTrue(subst.typeDomain().size() == 3);
    assertTrue(subst.get(beta).equals(type("Bool → $α")));

    subst = Matcher.match(x, fa);
    assertTrue(subst.domain().size() == 1);
    assertTrue(subst.get(x) == fa);
    assertTrue(subst.typeDomain().size() == 3);
    assertTrue(subst.get(beta).equals(type("Int")));

    subst = Matcher.match(x, fab);
    assertTrue(subst == null);
  }

  @Test
  public void testPolymorphicAbstractionBinderAlreadyKnown() {
    // f(x_α, h_{($α → $α) → A}(λx_α.g_{α → α}(x_α)))
    TVar alpha = TypeFactory.createVariable("α");
    Variable x = TermFactory.createBinder("x", alpha);
    Term g1 = TermFactory.createConstant("g", type("$α → $α"));
    Term h1 = TermFactory.createConstant("h", type("($α → $α) → A"));
    Term f1 = TermFactory.createConstant("f", type("$α → A → c($α)"));
    Term abs = TermFactory.createAbstraction(x, g1.apply(x));
    Term pattern = f1.apply(x).apply(h1.apply(abs));
    // f(a_{Int}, h(λy_{Int}.g_{Int → Int}(y_{Int})))
    Type itype = type("Int");
    Variable y = TermFactory.createBinder("y", itype);
    Term g2 = TermFactory.createConstant("g", type("Int → Int"));
    Term h2 = TermFactory.createConstant("h", type("(Int → Int) → A"));
    Term f2 = TermFactory.createConstant("f", type("Int → A → c(Int)"));
    Term a = TermFactory.createConstant("a", itype);
    Term hterm = h2.apply(TermFactory.createAbstraction(y, g2.apply(y)));
    Term instance = f2.apply(a).apply(hterm);

    MutableSubstitution subst = Matcher.match(pattern, instance);
    assertTrue(subst.get(alpha).equals(itype));
    assertTrue(subst.get(x).equals(a));
    assertTrue(subst.domain().size() == 1);

    // f(b_{Bool}, h(λy_{Int}.g_{Int → Int}(y_{Int}))) -- this should not work
    Term f3 = TermFactory.createConstant("f", type("Bool → A → c(Bool)"));
    Term b = TermFactory.createConstant("b", type("Bool"));
    instance = f3.apply(b).apply(hterm);
    assertTrue(Matcher.match(pattern, instance) == null);
  }

  @Test
  public void testPolymorphicAbstractionMatch() {
    // ( λx::α, y::β.f(A[x,y], B) ) C
    TVar alpha = TypeFactory.createVariable("α");
    TVar beta = TypeFactory.createVariable("β");
    Variable x = TermFactory.createBinder("x", alpha);
    Variable y = TermFactory.createBinder("y", beta);
    MetaVariable a = TermFactory.createMetaVar("A", type("$α -> $β -> c($α, $β)"), 2);
    Variable b = TermFactory.createVar("B", beta);
    Variable c = TermFactory.createVar("C", alpha);
    Term axy = TermFactory.createMeta(a, x, y);
    Term f = TermFactory.createConstant("f", type("c($α, $β) -> $β -> $α"));
    Term fterm = f.apply(axy).apply(b);
    Term abs = TermFactory.createAbstraction(x, TermFactory.createAbstraction(y, fterm));
    Term semipattern = abs.apply(c);
    // ( λv::Int -> Int, w::Int.f(g(3, v), 14) (λz.12 + z)
    Variable v = TermFactory.createBinder("v", type("Int -> Int"));
    Term g = TermFactory.createConstant("g", type("Int -> (Int -> Int) -> c(Int -> Int, Int)"));
    Term gterm = g.apply(TheoryFactory.createValue(3)).apply(v);
    Term f2 = TermFactory.createConstant("f", type("c(Int -> Int, Int) -> Int -> Int -> Int"));
    Term fterm2 = f2.apply(gterm).apply(TheoryFactory.createValue(3));
    Variable w = TermFactory.createBinder("w", type("Int"));
    Term abs1 = TermFactory.createAbstraction(v, TermFactory.createAbstraction(w, fterm2));
    Variable z = TermFactory.createBinder("z", type("Int"));
    Term twelve = TheoryFactory.createValue(12);
    Term abs2 = TermFactory.createAbstraction(z, TheoryFactory.plusSymbol.apply(twelve).apply(z));
    Term term = abs1.apply(abs2);

    MutableSubstitution subst = Matcher.match(semipattern, term);
    assertTrue(subst != null);
    assertTrue(subst.get(alpha).equals(type("Int -> Int")));
    assertTrue(subst.get(beta).equals(type("Int")));
    assertTrue(subst.get(x) == null);
    assertTrue(subst.get(a).equals(
      TermFactory.createAbstraction(v, TermFactory.createAbstraction(w, gterm))));
    assertTrue(subst.get(b).equals(TheoryFactory.createValue(3)));
    assertTrue(subst.get(c).equals(abs2));
  }
}

