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
import java.util.TreeMap;
import java.util.TreeSet;
import cora.exceptions.*;
import cora.types.Type;

public class AbstractionTest extends TermTestFoundation {
  @Test(expected = NullInitialisationError.class)
  public void testConstructWithNullBinder() {
    Term s = constantTerm("a", baseType("A"));
    new Abstraction(null, s);
  }

  @Test(expected = NullInitialisationError.class)
  public void testConstructWithNullSubterm() {
    Variable x = new Var("x", baseType("o"), true);
    new Abstraction(x, null);
  }

  @Test(expected = IllegalTermError.class)
  public void testConstructWithIllegalBinder() {
    Variable x = new Var("x", baseType("o"), false);
    Term s = constantTerm("a", baseType("A"));
    new Abstraction(x, s);
  }

  @Test
  public void testVariables() {
    Variable x = new Var("x", baseType("a"), true);
    Variable y = new Var("y", baseType("b"), true);
    Term f = constantTerm("f", arrowType(baseType("a"), arrowType("b", "c")));
    Term fxy = new Application(f, x, y);
    Term abs = new Abstraction(x, fxy); // λx.f(x,y)
    assertTrue(abs.vars().size() == 1);
    assertFalse(abs.vars().contains(x));
    assertTrue(abs.vars().contains(y));
    assertTrue(abs.boundVars().size() == 1);
    assertTrue(abs.boundVars().contains(x));
    assertFalse(abs.boundVars().contains(y));
  }

  /*
  @Test
  public void testWellbehavedness() {
    // TODO: test whether bound variales are recreated if the same variable occurs both free and
    // bound in a term, or is bound twice
  }
  */

  @Test
  public void testToStringBasics() {
    Variable x = new Var("x", baseType("o"), true);
    Term s = unaryTerm("f", baseType("a"), x);
    Term abs = new Abstraction(x, s);
    assertTrue(abs.toString().equals("λx.f(x)"));
    Variable y = new Var("y", baseType("a"), true);
    abs = new Abstraction(y, abs);
    assertTrue(abs.toString().equals("λy.λx.f(x)"));
  }

  @Test
  public void testRenaming() {
    // λx.λy.λu.f(g(z2,u),z1,x) where x and u have the same name, and z1 and z2 too
    Variable x = new Var("x", baseType("o"), true);
    Variable y = new Var("y", baseType("o"), true);
    Variable z1 = new Var("z", baseType("o"), true);
    Variable z2 = new Var("z", baseType("o"), true);
    Variable u = new Var("x", baseType("o"), true);
    Constant f = new Constant("f", arrowType(baseType("o"), arrowType(baseType("o"),
      arrowType("o", "o"))));
    Constant g = new Constant("g", arrowType(baseType("o"), arrowType("o", "o")));
    Term main = (new Application(f, new Application(g, z2, u), z1)).apply(x);
    Term abs = new Abstraction(x, new Abstraction(y, new Abstraction(u, main)));

    StringBuilder builder = new StringBuilder();
    TreeSet<String> set = new TreeSet<String>();
    TreeMap<Variable,String> renaming = new TreeMap<Variable,String>();

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
    Variable x1 = new Var("x", baseType("o"), true);
    Variable x2 = new Var("x", baseType("o"), true);
    Variable x3 = new Var("x", baseType("o"), true);
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

  @Test
  public void testBasics() {
    // λx.f(x, λy.y)
    Variable x = new Var("x", arrowType("o", "o"), true);
    Variable y = new Var("y", baseType("a"), true);
    Constant f = new Constant("f", arrowType(arrowType("o", "o"), arrowType(
      arrowType("a", "a"), baseType("b"))));
    Term abs = new Abstraction(x, new Application(f, x, new Abstraction(y, y)));

    assertTrue(abs.queryType().toString().equals("(o ⇒ o) ⇒ b"));
    assertFalse(abs.isVariable());
    assertFalse(abs.isConstant());
    assertFalse(abs.isFunctionalTerm());
    assertFalse(abs.isVarTerm());
    assertFalse(abs.isApplication());
    assertFalse(abs.isFirstOrder());
    assertTrue(abs.numberArguments() == 0);
    assertTrue(abs.queryArguments().size() == 0);
    assertTrue(abs.queryImmediateHeadSubterm(0) == abs);
    assertTrue(abs.queryAbstractionSubterm().equals(new Application(f, x, new Abstraction(y, y))));
    assertTrue(abs.queryHead() == abs);
    assertTrue(abs.queryVariable() == x);
    assertTrue(abs.apply(constantTerm("u", arrowType("o", "o"))).toString().equals(
      "(λx.f(x, λy.y))(u)"));
  }

  /*

  @Test(expected = InappropriatePatternDataError.class)
  public void testImmediateHeadSubterm() {
    // TODO: queryImmediateHeadSubterm(1)
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testRoot() {
    // TODO: queryRoot
  }

  @Test
  public void testPattern() {
    // TODO: both a pattern and a non-pattern
  }

  @Test
  public void testPositions() {
    // TODO: find positions and subterms at those positions
    // replace them too, and see how that changes alpha
    // (also do a replacement that still contains the binder at that position)
  }

  @Test
  public void testHeadPositions() {
    // TODO: find head positions and subterms at those head positions
    // replace them too, and see how that changes alpha
  }

  @Test(expected = IndexingError.class)
  public void testArgumentPositionRequest() {
    // TODO request an argument position
  }

  @Test(expected = IndexingError.class)
  public void testHeadPositionRequest() {
    // TODO: request an immediate head position 
  }

  @Test(expected = IndexingError.class)
  public void testBadPositionReplacement() {
    // TODO: try to replace at a position that doesn't exist
  }

  @Test(expected = IndexingError.class)
  public void testBadHeadPositionReplacement() {
    // TODO: try to replace a head position that doesn't exist
  }
  */

  @Test
  public void testAlphaEquals() {
    Var x = new Var("x", baseType("o"), true);
    Var y = new Var("u", baseType("o"), true);
    Var z = new Var("z", baseType("o"), true);
    Var u = new Var("u", baseType("o"), true);
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
    Var x = new Var("x", baseType("o"), true);
    Term term = new Abstraction(x, x);
    TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
    TreeMap<Variable,Integer> xi = new TreeMap<Variable,Integer>();
    mu.put(x, 1);
    term.alphaEquals(term, mu, xi, 2);
  }

  @Test(expected = IllegalTermError.class)
  public void testBinderAlreadyInXi() {
    Var x = new Var("x", baseType("o"), true);
    Term term = new Abstraction(x, x);
    TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
    TreeMap<Variable,Integer> xi = new TreeMap<Variable,Integer>();
    xi.put(x, 1);
    term.alphaEquals(term, mu, xi, 2);
  }

  @Test
  public void testEqualsWithDifferentBinderTypes() {
    Term a = constantTerm("q", baseType("o"));
    Var x = new Var("x", baseType("a"), true);
    Var y = new Var("x", baseType("b"), true);
    Term term1 = new Abstraction(x, a);
    Term term2 = new Abstraction(y, a);
    assertFalse(term1.equals(term2));
    assertTrue(term1.equals(new Abstraction(x, a)));
  }

  @Test
  public void testSimpleAlphaEquivalence() {
    Variable x = new Var("x", baseType("o"), true);
    Variable y = new Var("y", baseType("o"), true);
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
    Variable x = new Var("x", baseType("o"), true);
    Variable y = new Var("y", baseType("o"), true);
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
    Variable x = new Var("x", baseType("a"), true);
    Variable y = new Var("y", baseType("b"), true);
    Abstraction abs1 = new Abstraction(x, x);
    Abstraction abs2 = new Abstraction(x, y);

    assertFalse(abs1.equals(abs2));
    assertFalse(abs2.equals(abs1));
  }

}

