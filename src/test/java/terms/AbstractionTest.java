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

  /*
  @Test
  public void testBasics() {
    // TODO:
    // queryType
    // isVariable
    // isConstant
    // isFunctionalTerm
    // isVarTerm
    // isApplication
    // isFirstOrder
    // numberArguments
    // queryArguments
    // queryImmediateHeadSubterm
    // queryHead
    // queryVariable
    // apply
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

  @Test
  public void testAlphaEquality() {
    // TODO: check some things that are equal, and some that are not
  }
  */
}
