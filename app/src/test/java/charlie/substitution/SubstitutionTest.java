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
import charlie.types.Type;
import charlie.types.TVar;
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

public class SubstitutionTest {
  private Type type(String str) {
    return CoraParser.readType(str);
  }

  private TVar typevar(String name) {
    return TypeFactory.createVariable(name);
  }

  private Term constantTerm(String name, Type type) {
    return TermFactory.createConstant(name, type);
  }

  @Test
  public void testNullKeyCreation() {
    assertThrows(NullStorageException.class, () ->
      Substitution.of(null, constantTerm("37", type("Int"))));
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
    assertThrows(TypingException.class, () -> Substitution.of(x, xterm));
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
    Substitution gamma = Substitution.of();
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

    assertThrows(DuplicateMappingInSubstitutionException.class, () -> gamma.extend(x, xxterm));
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
    gamma.replace(y, yterm);
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

    gamma.replace(x, xxterm);
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

    gamma.replace(y, y);
    domain = gamma.domain();
    assertTrue(domain.contains(x));
    assertTrue(domain.contains(y));
    assertTrue(domain.size() == 2);
    
    gamma.delete(x);
    domain = gamma.domain();
    assertTrue(domain.size() == 1);
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
    Term term = subst.applySubstitution(abs);  // now term = λu.f(u, λz.z, x)

    // check that we got the right term
    assertFalse(term.equals(abs));
    assertTrue(term.equals(TermFactory.createAbstraction(u, f.apply(List.of(
      u, TermFactory.createAbstraction(z, z), x)))));
    assertEquals("λx__1.f(x__1, λz.z, x)", term.toString());

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
    assertTrue(gamma.applySubstitution(x).equals(xterm));
    assertTrue(gamma.applySubstitution(y).equals(x));
    assertTrue(gamma.applySubstitution(z).equals(z));
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

    Term q = gamma.applySubstitution(s);
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

    Term s = subst.applySubstitution(term);
    assertTrue(s.toString().equals(
      "(λx.λy__1.h(y__1, z))(a, f(λy__1.g(y__1, g(a, y))), f(λy__1.g(y__1, y__1)))"));
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

    Term s = subst.applySubstitution(term);
    assertTrue(s.toString().equals("h(f(λy__1.g(y__1, g(a, y))), z, f(λy__1.g(y__1, y__1)))"));
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
    assertTrue(gamma.applySubstitution(term).toString().equals("Z⟨λx__1.a(x__1, 1), λz.h(z, x)⟩"));
    // now try [x:=0, y:=1, F:=λz.h(z, x), Z := λF, G.F(G(0))]
    Variable g = TermFactory.createBinder("G", type("A -> A"));
    Term zero = constantTerm("0", type("A"));
    Term abs2 =
      TermFactory.createAbstraction(f, TermFactory.createAbstraction(g, f.apply(g.apply(zero))));
    gamma.extend(z, abs2);
    // result of substituting: [λF, G.F(G(0))]⟨λx.a(x,1), λz.h(z, x)⟩⟩ = (λx.a(x,1))(λz.h(z, x)(0))
    // (note that it isn't normalised beyond that)
    assertTrue(gamma.applySubstitution(term).toString().equals("(λx__1.a(x__1, 1))((λz.h(z, x))(0))"));
  }

  public void testPolymorphicExtendWithEmptyTypeMapping() {
    Variable x = TermFactory.createBinder("x", type("$alpha"));
    Term c = constantTerm("c", type("o -> o"));
    MutableSubstitution gamma = new MutableSubstitution();
    assertTrue(gamma.extend(x, c));
    assertTrue(gamma.get(typevar("alpha")).equals(type("o → o")));
    assertTrue(gamma.get(x) == c);
  }

  @Test
  public void testPolymorphicExtendWithExistingGoodTypeMapping() {
    TVar alpha = typevar("alpha");
    Variable x = TermFactory.createBinder("x", type("$alpha"));
    Term c = constantTerm("c", type("o -> o"));
    MutableSubstitution gamma = new MutableSubstitution();
    assertTrue(gamma.extend(alpha, type("o → o")));
    assertTrue(gamma.extend(x, c));
    assertTrue(gamma.typeDomain().size() == 1);
    assertTrue(gamma.get(x) == c);
  }

  @Test
  public void testPolymorphicExtendWithExistingBadMapping() {
    TVar alpha = typevar("alpha");
    Variable x = TermFactory.createBinder("x", type("$alpha"));
    Term c = constantTerm("c", type("o -> o"));
    MutableSubstitution gamma = new MutableSubstitution();
    assertTrue(gamma.extend(alpha, alpha));
    assertThrows(TypingException.class, () -> gamma.extend(x, c));
  }

  @Test
  public void testPolymorphicExtendWithPartiallyExistingMapping() {
    // create Z :: [α] → β
    TVar alpha = typevar("alpha");
    TVar beta = typevar("beta");
    MetaVariable z = TermFactory.createMetaVar("Z", type("$alpha → $beta"), 1);
    // create λx::o.f(x)_γ
    TVar gamma = typevar("gamma");
    Type o = type("o");
    Variable x = TermFactory.createBinder("x", o);
    Term fx = constantTerm("f", type("o → $gamma")).apply(x);
    Term abs = TermFactory.createAbstraction(x, fx);
    // create subst = [β:=γ]
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(beta, gamma);
    // add Z := λx::o.f(x) to subst
    assertTrue(subst.extend(z, abs));
    assertTrue(subst.domain().size() == 1);
    assertTrue(subst.get(z) == abs);
    assertTrue(subst.typeDomain().size() == 2);
    assertTrue(subst.get(alpha).equals(o));
    assertTrue(subst.get(beta).equals(gamma));
    // create subst2 = [α:=o], and add the same mapping
    MutableSubstitution subst2 = new MutableSubstitution();
    assertTrue(subst2.extend(alpha, o));
    subst2.replace(z, abs);
    assertTrue(subst2.get(z) == abs);
    assertTrue(subst2.domain().size() == 1);
    assertTrue(subst2.typeDomain().size() == 2);
    assertTrue(subst2.get(alpha).equals(o));
    assertTrue(subst2.get(beta).equals(gamma));
  }

  @Test
  public void testPolymorphicExtensionFailure() {
    TVar alpha = typevar("alpha");
    TVar beta = typevar("beta");
    TVar gamma = typevar("gamma");
    Type osort = type("o");
    // create subst = [β:=o]
    MutableSubstitution subst = new MutableSubstitution();
    assertTrue(subst.extend(beta, osort));
    // ensure that trying to override an existing type mapping won't work
    assertFalse(subst.extend(beta, type("o")));
    assertThrows(DuplicateMappingInSubstitutionException.class, () -> subst.extend(beta, gamma));
    assertTrue(subst.typeDomain().size() == 1);
    assertTrue(subst.get(beta) == osort);
    // create Z :: ⟨meh⟩ → α
    MetaVariable z = TermFactory.createMetaVar("Z", type("meh -> $alpha"), 1);
    // create abs = λx::o.f(x)_γ
    Variable x = TermFactory.createBinder("x", osort);
    Term fx = constantTerm("f", type("o → $gamma")).apply(x);
    Term abs = TermFactory.createAbstraction(x, fx);
    // fail to add Z := abs to subst
    assertThrows(TypingException.class, () -> subst.extend(z, abs));
    assertTrue(subst.typeDomain().size() == 1);
    assertTrue(subst.get(beta) == osort);
    // fail to add u_{c(α,β)} := v_{c(A,B)} to subst
    Variable u = TermFactory.createVar("u", type("c($alpha,$beta)"));
    Variable v = TermFactory.createVar("v", type("c(A,B)"));
    assertThrows(TypingException.class, () -> subst.extend(u, v));
    assertTrue(subst.typeDomain().size() == 1);
    assertTrue(subst.get(beta) == osort);
    assertTrue(subst.domain().size() == 0);
  }

  @Test
  public void testRemovePolymorphicVariable() {
    TVar alpha = typevar("alpha");
    Variable x = TermFactory.createVar("x", alpha);
    Term a = constantTerm("a", type("AA"));
    MutableSubstitution subst = new MutableSubstitution(x, a);
    subst.delete(x);
    assertTrue(subst.domain().size() == 0);
    assertTrue(subst.typeDomain().size() == 1);
    assertTrue(subst.get(alpha).equals(type("AA")));
  }

  @Test
  public void testSuccessfulPolymorphicReplace() {
    TVar alpha = typevar("alpha");
    TVar beta = typevar("beta");
    Variable x = TermFactory.createBinder("x", alpha);
    Variable y = TermFactory.createVar("y", beta);
    Variable z = TermFactory.createBinder("z", beta);
    MutableSubstitution subst = new MutableSubstitution(x, y);
    subst.replace(x, z);
    assertTrue(subst.get(x) == z);
    subst.replace(x, y);
    assertTrue(subst.get(x) == y);
  }

  @Test
  public void testFailedPolymorphicReplace() {
    TVar alpha = typevar("alpha");
    TVar beta = typevar("beta");
    Type osrt = type("o");
    Variable x = TermFactory.createBinder("x", alpha);
    Variable y = TermFactory.createVar("y", beta);
    Term zero = constantTerm("zero", osrt);
    MutableSubstitution subst = new MutableSubstitution(x, y);
    try { subst.replace(x, zero); }
    catch (TypingException e) {
      assertTrue(e.getMessage().equals("Cannot replace mapping for x (of instantiated type " +
        "$beta) to value zero (of type o) in substitution."));
      return;
    }
    assertTrue(false, "Expected a TypingException, did not get one.");
  }

  @Test
  public void testSubstitutePolymorphicVariable() {
    TVar alpha = typevar("alpha");
    Variable x = TermFactory.createVar("x", alpha);
    Term ak = constantTerm("ak", type("A -> A"));
    MutableSubstitution subst = new MutableSubstitution(x, ak);
    Term result = subst.applySubstitution(x);
    assertTrue(result == ak);
  }

  @Test
  public void testSubstitutePolymorphicVariableNotInDomain() {
    TVar alpha = typevar("alpha");
    Variable x = TermFactory.createVar("x", type("$alpha -> $beta"));
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(alpha, alpha);
    assertTrue(subst.applySubstitution(x) == x);
  }

  @Test
  public void testSubstitutePolymorphicVariableOutsideDomainButWithMappedTypeVariables() {
    TVar alpha = typevar("alpha");
    TVar beta = typevar("beta");
    Variable x = TermFactory.createVar("x", type("$alpha -> $beta"));
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(beta, alpha);
    assertThrows(PolymorphicSubstitutionException.class, () -> subst.applySubstitution(x));
  }

  @Test
  public void testSubstituteMonomorphicSymbol() {
    Term cons = TermFactory.createConstant("cons", type("Int -> list -> list"));
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(typevar("α"), type("Int → $β"));
    Term result = subst.applySubstitution(cons);
    assertTrue(result == cons);
  }

  @Test
  public void testSubstitutePolymorphicSymbol() {
    Term cons = TermFactory.createConstant("cons", type("$α → list($α) → list($α)"));
    MutableSubstitution subst = new MutableSubstitution();
    subst.extend(typevar("α"), type("Int → $β"));
    Term result = subst.applySubstitution(cons);
    assertTrue(result.isConstant());
    assertTrue(result.queryType().equals(type("(Int → $β) → list(Int → $β) → list(Int → $β)")));
  }

  @Test
  public void testSubstitutePolymorphicMetaApplication() {
    // Z_{α → h(β) → α}[x,c]
    TVar alpha = typevar("alpha");
    TVar beta = typevar("beta");
    Type ztype = type("$alpha -> h($beta) -> $alpha");
    Variable x = TermFactory.createVar("x", alpha);
    Term c = constantTerm("c", type("h($beta)"));
    MetaVariable z = TermFactory.createMetaVar("Z", ztype, 2);
    Term term = TermFactory.createMeta(z, x, c);
    // substitution [α:=γ,β:=Bool,x:=y,Z:=λuv.g(v,u)]
    TVar gamma = typevar("gamma");
    MutableSubstitution subst = new MutableSubstitution(x, TermFactory.createVar("y", gamma));
    subst.extend(beta, type("Bool"));
    Variable u = TermFactory.createBinder("u", gamma);
    Variable v = TermFactory.createBinder("v", type("h(Bool)"));
    Term gvu = TermFactory.createApp(constantTerm("g", type("h(Bool) -> $gamma -> $gamma")), v, u);
    subst.extend(z, TermFactory.createAbstraction(u, TermFactory.createAbstraction(v, gvu)));
    // apply it!
    Term result = subst.applySubstitution(term);
    assertTrue(result.queryType().equals(gamma));
    assertTrue(result.toString().equals("g(c, y)"));
  }

  @Test
  public void testMissingPolymorphicMetaVariableWithAcceptableTypeVariable() {
    // Z_{α → h(β) → α}[x,c]
    TVar alpha = typevar("alpha");
    TVar beta = typevar("beta");
    Type ztype = type("$alpha -> h($beta) -> $alpha");
    Variable x = TermFactory.createVar("x", alpha);
    Term c = constantTerm("c", type("h($beta)"));
    MetaVariable z = TermFactory.createMetaVar("Z", ztype, 2);
    Term term = TermFactory.createMeta(z, x, c);
    // substitution [α:=α,x:=y]
    Variable y = TermFactory.createVar("y", alpha);
    MutableSubstitution subst = new MutableSubstitution(x, y);
    // apply it!
    Term result = subst.applySubstitution(term);
    assertTrue(result.queryType().equals(alpha));
    assertTrue(result.toString().equals("Z⟨y, c⟩"));
  }

  @Test
  public void testMissingPolymorphicMetaVariableWithBadTypeVariable() {
    // Z_{α → h(β) → α}[x,c]
    TVar alpha = typevar("alpha");
    TVar beta = typevar("beta");
    Type ztype = type("$alpha -> h($beta) -> $alpha");
    Variable x = TermFactory.createVar("x", alpha);
    Term c = constantTerm("c", type("h($beta)"));
    MetaVariable z = TermFactory.createMetaVar("Z", ztype, 2);
    Term term = TermFactory.createMeta(z, x, c);
    // substitution [α:=α,β:=γ,x:=y]
    Variable y = TermFactory.createVar("y", alpha);
    MutableSubstitution subst = new MutableSubstitution(x, y);
    TVar gamma = typevar("gamma");
    subst.extend(beta, gamma);
    // apply it!
    assertThrows(PolymorphicSubstitutionException.class, () -> subst.applySubstitution(term));
  }

  @Test
  public void testSubstitutePolymorphicApplication() {
    TVar alpha = typevar("alpha");
    TVar beta = typevar("beta");
    TVar gamma = typevar("gamma");
    Type xtype = type("$alpha -> $beta");
    Variable x = TermFactory.createVar("x", xtype);
    Type ztype = type("($gamma -> Int) -> $beta -> $gamma");
    Variable z = TermFactory.createVar("z", ztype);
    Term a = constantTerm("a", alpha);
    Term appl = x.apply(a);
    MutableSubstitution subst = new MutableSubstitution(x, z);
    Term substituted = subst.applySubstitution(appl);
    assertTrue(substituted.toString().equals("z(a)"));
    assertTrue(substituted.equals(z.apply(constantTerm("a", type("$gamma -> Int")))));
  }

  @Test
  public void testSubstitutePolymorphicAbstraction() {
    TVar alpha = typevar("alpha");
    TVar beta = typevar("beta");
    Variable x = TermFactory.createBinder("x", type("$alpha -> $beta"));
    Variable z = TermFactory.createVar("z", type("$gamma"));
    Term f = constantTerm("f", type("($alpha -> $beta) -> $gamma -> A"));
    Term abs = TermFactory.createAbstraction(x, f.apply(x).apply(z));
      // λx_{α → β}.f(x_{α → β}, z_γ)

    Term bb = constantTerm("BB", type("Bool -> Bool"));
    MutableSubstitution subst = new MutableSubstitution(z, bb);
    subst.extend(alpha, type("Int"));
      // [α := Int, γ := Bool →  Bool, z := BB]

    Term substituted = subst.applySubstitution(abs);

    // did we get λy_{Int → β}.f(y_{Int → β}, BB) out?
    Variable y = TermFactory.createBinder("y", type("Int -> $beta"));
    Term ff = constantTerm("f", type("(Int -> $beta) -> (Bool -> Bool) -> A"));
    Term newabs = TermFactory.createAbstraction(y, ff.apply(y).apply(bb));
    assertTrue(substituted.equals(newabs));

    // is the substitution unmodified?
    assertTrue(subst.domain().size() == 1);
    assertTrue(subst.typeDomain().size() == 2);
    assertTrue(subst.get(alpha).equals(type("Int")));
    assertFalse(subst.typeDomain().contains(beta));
    assertTrue(subst.get(typevar("gamma")).equals(type("Bool -> Bool")));
    assertTrue(subst.get(y) == null);
    assertTrue(subst.get(z) == bb);
  }

  // if I should ever want to implement "combine":
  // α := β, γ := δ → α combined with α := A, β := B, becomes α := B, γ := δ → A
  // if X_γ is added to that, mapped to f_{δ → α}, then it becomes f_{δ →  A}
  // if Y_{α → β} is mapped to Z_{β → β}, and Z does not occur in the other mapping => exception
  // if the second mapping maps Z_α to f_A => exception
  // if the second mapping maps Z_δ to f_A, the combined mapping should do the same
}

