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
import charlie.parser.CoraParser;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.MetaVariable;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.FunctionSymbol;
import charlie.terms.TypingException;
import charlie.terms.TermFactory;
import charlie.terms.TheoryFactory;

public class SubstitutionTest {
  private Type type(String str) {
    return CoraParser.readType(str);
  }

  private Term constantTerm(String name, Type type) {
    return TermFactory.createConstant(name, type);
  }

  @Test
  public void testNullKeyCreation() {
    assertThrows(NullStorageException.class, () ->
      new MutableSubstitution(null, constantTerm("37", type("Int"))));
  }

  @Test
  public void testNullValueCreation() {
    assertThrows(NullStorageException.class, () ->
      new MutableSubstitution(TermFactory.createVar("x", type("Int")), null));
  }

  @Test
  public void testIlltypedCreation() {
    Variable x = TermFactory.createVar("x", type("Int"));
    Term xterm = constantTerm("false", type("Bool"));
    assertThrows(TypingException.class, () -> new MutableSubstitution(x, xterm));
  }

  @Test
  public void testIncorrectArityInCreation() {
    MetaVariable x = TermFactory.createMetaVar("x", type("o -> o"), 1);
    Term xterm = constantTerm("a", type("o -> o"));
    assertThrows(TypingException.class, () -> new MutableSubstitution(x, xterm));
  }
 
  @Test
  public void testNullKeyExtension() {
    MutableSubstitution gamma = new MutableSubstitution();
    Variable x = TermFactory.createVar("x", type("o"));
    assertThrows(NullStorageException.class, () -> gamma.extend(null, x));
  }

  @Test
  public void testNullValueExtension() {
    MutableSubstitution gamma = new MutableSubstitution();
    Variable x = TermFactory.createVar("x", type("o"));
    assertThrows(NullStorageException.class, () -> gamma.extend(x, null));
  }

  @Test
  public void testIncorrectArityExtension() {
    MetaVariable z = TermFactory.createMetaVar("z", type("o -> o"), 0);
    Term zterm = constantTerm("a", type("o -> o"));
    MutableSubstitution gamma = new MutableSubstitution(z, zterm);
    MetaVariable y = TermFactory.createMetaVar("y", type("o -> o"), 1);
    assertThrows(TypingException.class, () -> gamma.extend(y, zterm));
  }

  @Test
  public void testIllTypedExtension() {
    Variable x = TermFactory.createVar("x", type("Int"));
    Term xterm = constantTerm("37", type("Int"));
    MutableSubstitution gamma = new MutableSubstitution(x, xterm);
    assertThrows(TypingException.class, () -> gamma.extend(
      TermFactory.createVar("y", type("Int")), constantTerm("false", type("Bool"))));
  }

  @Test
  public void testNullKeyReplacement() {
    Variable x = TermFactory.createVar("x", type("Int"));
    Term xterm = constantTerm("37", type("Int"));
    MutableSubstitution gamma = new MutableSubstitution(x, xterm);
    assertThrows(NullStorageException.class, () -> gamma.replace(null, xterm));
  }
  
  @Test
  public void testNullValueReplacement1() {
    Variable x = TermFactory.createVar("x", type("Int"));
    Term xterm = constantTerm("37", type("Int"));
    MutableSubstitution gamma = new MutableSubstitution(x, xterm);
    assertThrows(NullStorageException.class, () -> gamma.replace(x, null));
  }

  @Test
  public void testIllTypedReplacement() {
    Variable x = TermFactory.createVar("x", type("Int"));
    Term xterm = constantTerm("37", type("Int"));
    MutableSubstitution gamma = new MutableSubstitution(x, xterm);
    assertThrows(TypingException.class, () ->
      gamma.replace(x, constantTerm("false", type("Bool"))));
  }

  @Test
  public void testIncorrectArityReplacement() {
    MetaVariable z = TermFactory.createMetaVar("z", type("o -> o"), 1);
    Variable x = TermFactory.createBinder("x", type("o"));
    Term zterm = TermFactory.createAbstraction(x, x);
    MutableSubstitution gamma = new MutableSubstitution(z, zterm);
    assertThrows(TypingException.class, () ->
      gamma.replace(z, constantTerm("37", zterm.queryType())));
  }

 @Test
  public void testEmptySubstitutionBasics() {
    Substitution gamma = new MutableSubstitution();
    Variable x = TermFactory.createVar("x", type("o"));
    assertTrue(gamma.get(x) == null);
    assertTrue(gamma.getReplacement(x).equals(x));
  }

  @Test
  public void testExtendingWithNewKey() {
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("o"));
    Variable z = TermFactory.createVar("z", type("o"));
    Term xterm = constantTerm("37", type("Int"));
    Term yterm = z;

    MutableSubstitution gamma = new MutableSubstitution(x, xterm);
    assertTrue(gamma.extend(y, yterm));
    assertTrue(gamma.get(x).equals(xterm));
    assertTrue(gamma.get(y).equals(yterm));
    assertTrue(gamma.getReplacement(z).equals(z));
  }

  @Test
  public void testCopy() {
    Variable x = TermFactory.createVar("x", type("Int"));
    Term xterm = constantTerm("37", type("Int"));
    Substitution gamma = new MutableSubstitution(x, xterm);
    MutableSubstitution delta = gamma.copy();
    Variable y = TermFactory.createVar("y", type("o"));
    Term yterm = TermFactory.createVar("z", type("o"));
    delta.extend(y, yterm);
    assertTrue(gamma.get(x) == xterm);
    assertTrue(gamma.get(y) == null);
    assertTrue(delta.get(x) == xterm);
    assertTrue(delta.get(y) == yterm);
  }

  @Test
  public void testExtendingWithMetavariable() {
    MetaVariable z = TermFactory.createMetaVar("z", type("o -> o"), 1);
    Variable x = TermFactory.createBinder("x", type("o"));
    Term zterm = TermFactory.createAbstraction(x, x);
    MutableSubstitution gamma = new MutableSubstitution(z, zterm);
    MetaVariable y = TermFactory.createMetaVar("y", type("o -> o"), 1);
    assertTrue(gamma.get(z).equals(zterm));
    assertTrue(gamma.get(y) == null);
    assertTrue(gamma.extend(y, zterm));
  }

  @Test
  public void testExtendingWithExistingKey() {
    Variable x = TermFactory.createVar("x", type("Int"));
    Term xterm = constantTerm("37", type("Int"));
    Term xxterm = constantTerm("42", type("Int"));

    MutableSubstitution gamma = new MutableSubstitution(x, xterm);

    assertFalse(gamma.extend(x, xxterm));
    assertTrue(gamma.getReplacement(x).equals(xterm));
  }

  @Test
  public void testReplacingWithNewKey() {
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("o"));
    Variable z = TermFactory.createVar("z", type("o"));
    Term xterm = constantTerm("37", type("Int"));
    Term yterm = z;

    MutableSubstitution gamma = new MutableSubstitution(x, xterm);
    assertFalse(gamma.replace(y, yterm));
    assertTrue(gamma.get(x).equals(xterm));
    assertTrue(gamma.get(y).equals(yterm));
    assertTrue(gamma.getReplacement(z).equals(z));
  }

  @Test
  public void testReplacingWithExistingKey() {
    Variable x = TermFactory.createVar("x", type("Int"));
    Term xterm = constantTerm("37", type("Int"));
    Term xxterm = constantTerm("42", type("Int"));

    MutableSubstitution gamma = new MutableSubstitution(x, xterm);

    assertTrue(gamma.replace(x, xxterm));
    assertTrue(gamma.get(x).equals(xxterm));
  }

  @Test
  public void testRemoving() {
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("o"));
    Variable z = TermFactory.createVar("z", type("o"));

    Term xterm = constantTerm("37", type("Int"));
    Term yterm = z;

    MutableSubstitution gamma = new MutableSubstitution();
    assertTrue(gamma.extend(x, xterm));
    assertTrue(gamma.extend(y, yterm));
    gamma.delete(y);
    gamma.delete(z);
    assertTrue(gamma.getReplacement(x).equals(xterm));
    assertTrue(gamma.getReplacement(y).equals(y));
    assertTrue(gamma.get(y) == null);
    assertTrue(gamma.getReplacement(z).equals(z));
  }

  @Test
  public void testDomain() {
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("o"));
    Variable z = TermFactory.createVar("z", type("o"));

    Term xterm = constantTerm("37", type("Int"));
    Term yterm = z;

    MutableSubstitution gamma = new MutableSubstitution();
    gamma.extend(x, xterm);
    gamma.extend(y, yterm);
    Set<Replaceable> domain = gamma.domain();

    assertTrue(domain.contains(x));
    assertTrue(domain.contains(y));
    assertTrue(domain.size() == 2);

    assertTrue(gamma.replace(y, y));
    domain = gamma.domain();
    assertTrue(domain.contains(x));
    assertTrue(domain.contains(y));
    assertTrue(domain.size() == 2);
    
    gamma.delete(x);
    domain = gamma.domain();
    assertTrue(domain.size() == 1);
  }

  @Test
  public void testSubstitute() {
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Variable z = TermFactory.createVar("z", type("Int"));
    Variable a = TermFactory.createVar("a", type("Int"));
    Variable b = TermFactory.createVar("b", type("Int"));
    FunctionSymbol f = TermFactory.createConstant("f", type("Int -> Int -> Int"));
    Term one = TheoryFactory.createValue(1);
    Term two = TheoryFactory.createValue(2);
    MutableSubstitution gamma = new MutableSubstitution();
    gamma.extend(x, f.apply(y).apply(z));                     // γ(x) = f(y, z)
    gamma.extend(y, f.apply(z).apply(f.apply(one).apply(a))); // γ(y) = f(z, f(1, a))
    MutableSubstitution delta = new MutableSubstitution();
    delta.extend(y, two);                                     // δ(y) = 2
    delta.extend(z, f.apply(x).apply(one));                   // δ(z) = f(x, 1)
    delta.extend(b, a);                                       // δ(b) = a
    gamma.substitute(delta);
    assertTrue(gamma.domain().size() == 4);
    assertTrue(gamma.domain().contains(x));
    assertTrue(gamma.domain().contains(y));
    assertTrue(gamma.domain().contains(z));
    assertTrue(gamma.domain().contains(b));
    assertFalse(gamma.domain().contains(a));
    assertTrue(gamma.getReplacement(x).toString().equals("f(2, f(x, 1))"));
    assertTrue(gamma.getReplacement(y).toString().equals("f(f(x, 1), f(1, a))"));
    assertTrue(gamma.getReplacement(z).toString().equals("f(x, 1)"));
    assertTrue(gamma.getReplacement(b).toString().equals("a"));
    assertTrue(delta.getReplacement(z).toString().equals("f(x, 1)"));
  }

  @Test
  public void testMakeImmutable() {
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("o"));
    Variable z = TermFactory.createVar("z", type("o"));

    Term xterm = constantTerm("37", type("Int"));
    Term yterm = z;

    MutableSubstitution gamma = new MutableSubstitution();
    Substitution delta = gamma.makeImmutable();
    gamma.extend(x, xterm);
    gamma.extend(y, yterm);
    assertTrue(delta.domain().size() == 2);
    assertFalse(delta instanceof MutableSubstitution);
    assertTrue(delta.makeImmutable() == delta);
  }

  @Test
  public void testSubstituteAbstraction() {
    // λx.f(x, λz.z, y)
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createVar("y", type("o"));
    Variable z = TermFactory.createBinder("z", type("o"));
    Variable u = TermFactory.createBinder("u", type("o"));
    Term f = constantTerm("f", type("o -> (o -> o) -> o -> o"));
    Term abs = TermFactory.createAbstraction(x, f.apply(x).apply(
      TermFactory.createAbstraction(z, z)).apply(y));

    // [x:=y, y:=x]
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(x, y); 
    subst.extend(y, x); 
    Term term = subst.apply(abs);  // now term = λu.f(u, λz.z, x)

    // check that we got the right term
    assertFalse(term.equals(abs));
    assertTrue(term.equals(TermFactory.createAbstraction(u, f.apply(List.of(
      u, TermFactory.createAbstraction(z, z), x)))));
    assertEquals("λx1.f(x1, λz.z, x)", term.toString());

    // check that all binders are fresh
    assertEquals(1, term.queryVariable().compareTo(u));
    assertEquals(1, term.queryAbstractionSubterm().queryArgument(2).queryVariable().compareTo(u));

    // check that subst is unchanged
    assertTrue(subst.domain().size() == 2);
    assertTrue(subst.get(x) == y);
    assertTrue(subst.get(y) == x);
  }

  @Test
  public void testSubstituteVariable() {
    Variable x = TermFactory.createBinder("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Variable z = TermFactory.createBinder("z", type("Bool"));
    Term xterm = constantTerm("37", type("Int"));
    MutableSubstitution gamma = new MutableSubstitution(x, xterm);
    gamma.extend(y, x); 
    assertTrue(gamma.apply(x).equals(xterm));
    assertTrue(gamma.apply(y).equals(x));
    assertTrue(gamma.apply(z).equals(z));
  }

  @Test
  public void testApplicationSubstitutionApplicative() {
    Variable x = TermFactory.createBinder("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Variable z = TermFactory.createVar("Z", type("Int -> Bool -> Int"));
    Term s = z.apply(List.of(x, constantTerm("f", type("Int -> Bool")).apply(y))); // Z(x, f(y))

    Term thirtyseven = constantTerm("37", type("Int"));
    Term g = constantTerm("g", type("o -> Int -> Bool -> Int"));
    Term t = g.apply(constantTerm("c", type("o")));

    MutableSubstitution gamma = new MutableSubstitution(x, thirtyseven);
    gamma.extend(y, x);
    gamma.extend(z, t);

    Term q = gamma.apply(s);
    assertTrue(q.toString().equals("g(c, 37, f(x))"));
  }

  @Test
  public void testApplicationSubstitutionLambda() {
    // X(a, f(λy.g(y, z)), f(λy.g(y, y)))
    Term g = constantTerm("g", type("o -> o -> o"));
    Term f = constantTerm("f", type("(o -> o) -> o"));
    Term a = constantTerm("a", type("o"));
    Variable x = TermFactory.createBinder("X", type("o -> o -> o -> o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Variable z = TermFactory.createBinder("z", type("o"));
    Term term = x.apply(List.of(a,
      f.apply(TermFactory.createAbstraction(y, g.apply(List.of(y, z)))),
      f.apply(TermFactory.createAbstraction(y, g.apply(List.of(y, y))))));
    // [X := λxy.h(y, z), y := a, z := g(a, y)]
    Term h = constantTerm("h", type("o -> o -> o -> o"));
    Variable x1 = TermFactory.createBinder("x", type("o"));
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(x, TermFactory.createAbstraction(x1,
      TermFactory.createAbstraction(y, h.apply(List.of(y, z)))));
    subst.extend(y, a);
    subst.extend(z, g.apply(List.of(a, y)));

    Term s = subst.apply(term);
    assertTrue(s.toString().equals("(λx.λy1.h(y1, z))(a, f(λy1.g(y1, g(a, y))), f(λy1.g(y1, y1)))"));
  }

  @Test
  public void testMetaApplicationSubstitutionLambda() {
    // X[a, f(λy.g(y, z))](f(λy.g(y, y)))
    Term g = constantTerm("g", type("o -> o -> o"));
    Term f = constantTerm("f", type("(o -> o) -> o"));
    Term a = constantTerm("a", type("o"));
    MetaVariable x = TermFactory.createMetaVar("X", type("o -> o -> o -> o"), 2);
    Variable y = TermFactory.createBinder("y", type("o"));
    Variable z = TermFactory.createBinder("z", type("o"));
    Term term = TermFactory.createMeta(x, List.of(a,
      f.apply(TermFactory.createAbstraction(y, g.apply(List.of(y, z)))))).apply(
      f.apply(TermFactory.createAbstraction(y, g.apply(List.of(y, y)))));
    // [X := λxy.h(y, z), y := a, z := g(a, y)]
    Term h = constantTerm("h", type("o -> o -> o -> o"));
    Variable x1 = TermFactory.createBinder("x", type("o"));
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(x, TermFactory.createAbstraction(x1,
      TermFactory.createAbstraction(y, h.apply(List.of(y, z)))));
    subst.extend(y, a);
    subst.extend(z, g.apply(List.of(a, y)));

    Term s = subst.apply(term);
    assertTrue(s.toString().equals("h(f(λy1.g(y1, g(a, y))), z, f(λy1.g(y1, y1)))"));
  }

  @Test
  public void testDifficultMetaSubstitution() {
    // Z⟨λx.a(x,y),F⟩
    Variable x = TermFactory.createBinder("x", type("A"));
    Variable y = TermFactory.createBinder("y", type("B"));
    Term a = constantTerm("a", type("A -> B -> A"));
    Term abs = TermFactory.createAbstraction(x, TermFactory.createApp(a, x, y));
    Variable f = TermFactory.createBinder("F", type("A -> A"));
    MetaVariable z = TermFactory.createMetaVar("Z", type("(A -> A) -> (A -> A) -> A"), 2);
    Term term = TermFactory.createMeta(z, abs, f);
    // first try [x:=0, y:=1, F:=λz.h(z, x)]; this should be pretty simple
    MutableSubstitution gamma = new MutableSubstitution();
    gamma.extend(x, constantTerm("0", type("A")));
    gamma.extend(y, constantTerm("1", type("B")));
    Variable z2 = TermFactory.createBinder("z", type("A"));
    Term h = constantTerm("h", type("A -> A -> A"));
    Term abs1 = TermFactory.createAbstraction(z2, TermFactory.createApp(h, z2, x));
    gamma.extend(f, abs1);
    assertTrue(gamma.apply(term).toString().equals("Z⟨λx1.a(x1, 1), λz.h(z, x)⟩"));
    // now try [x:=0, y:=1, F:=λz.h(z, x), Z := λF, G.F(G(0))]
    Variable g = TermFactory.createBinder("G", type("A -> A"));
    Term zero = constantTerm("0", type("A"));
    Term abs2 =
      TermFactory.createAbstraction(f, TermFactory.createAbstraction(g, f.apply(g.apply(zero))));
    gamma.extend(z, abs2);
    // result of substituting: [λF, G.F(G(0))]⟨λx.a(x,1), λz.h(z, x)⟩⟩ = (λx.a(x,1))(λz.h(z, x)(0))
    // (note that it isn't normalised beyond that)
    assertTrue(gamma.apply(term).toString().equals("(λx1.a(x1, 1))((λz.h(z, x))(0))"));
  }

  @Test
  public void testSubstituteTuple() {
    Term a = constantTerm("a", type("N"));
    Variable x = TermFactory.createBinder("x", type("N"));
    Term abs = TermFactory.createAbstraction(x, constantTerm("f", type("N -> M")).apply(x));
    Variable y = TermFactory.createVar("y", type("P"));
    Variable z = TermFactory.createVar("z", type("P -> P"));
    Term fa = constantTerm("f", type("N -> M")).apply(a);
    Term s = TermFactory.createTuple(a, abs, TermFactory.createTuple(fa, y));
    Substitution gamma = new MutableSubstitution(y, constantTerm("q", type("P")));
    Term t = gamma.apply(s);
    assertTrue(t.toString().equals("⦇a, λx.f(x), ⦇f(a), q⦈⦈"));
  }
}

