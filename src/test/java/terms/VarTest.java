/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

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
import java.util.List;
import java.util.TreeMap;
import java.util.TreeSet;
import cora.exceptions.*;
import cora.types.Type;

public class VarTest extends TermTestFoundation {
  @Test(expected = NullInitialisationError.class)
  public void testNullName() {
    Variable x = new Var(null, baseType("o"));
  }

  @Test(expected = NullInitialisationError.class)
  public void testNullType() {
    Variable x = new Var("x", null);
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testRootRequest() {
    Variable x = new Var("x", baseType("o"));
    x.queryRoot();
  }

  @Test(expected = IndexingError.class)
  public void testSubtermRequest() {
    Variable x = new Var("x", baseType("o"));
    x.queryArgument(1);
  }

  @Test(expected = NullCallError.class)
  public void testNullSubstitution() {
    Term t = new Var("x", baseType("Int"));
    t.substitute(null);
  }

  @Test(expected = NullCallError.class)
  public void testNullMatch1() {
    Term t = new Var("x", baseType("Int"));
    t.match(constantTerm("37", baseType("Int")), null);
  }

  @Test(expected = NullCallError.class)
  public void testNullMatch2() {
    Term t = new Var("x", baseType("Int"));
    Substitution subst = new Subst();
    t.match(null, subst);
  }

  @Test(expected = ArityError.class)
  public void testBaseVariableApplication() {
    Term t = new Var("x", baseType("Int"));
    t.apply(t);
  }

  @Test(expected = TypingError.class)
  public void testIllegalTypeApplication() {
    Term t = new Var("x", arrowType("a", "b"));
    Term q = constantTerm("c", baseType("b"));
    t.apply(q);
  }

  @Test
  public void testTermVarBasics() {
    Variable x = new Var("x", baseType("o"));
    Term s = x;
    assertTrue(s.isVariable());
    assertTrue(s.isVarTerm());
    assertFalse(s.isConstant());
    assertFalse(s.isFunctionalTerm());
    assertTrue(s.queryVariable().equals(x));
    assertTrue(s.queryHead().equals(x));
    assertTrue(s.toString().equals("x"));
    assertTrue(s.numberArguments() == 0);
    assertTrue(s.queryArguments().size() == 0);
    assertTrue(s.isPattern());
    assertTrue(s.isFirstOrder());
    assertFalse(s.isApplication());
    assertTrue(s.isApplicative());
    assertTrue(s.isClosed());
    assertFalse(s.isGround());
    assertTrue(s.refreshBinders() == s);
    assertFalse(x.isBinderVariable());
    Variable z = new Var("z", arrowType("o", "o"));
    assertFalse(z.isFirstOrder());
    assertTrue(z.isPattern());
    assertTrue(z.isApplicative());
    assertTrue(z.apply(x).equals(new Application(z, x)));
    assertFalse(z.apply(x).isPattern());
    Variable y = new Binder("x", baseType("o"));
    assertTrue(x.compareTo(y) == -1);
  }

  @Test
  public void testTermVarReplaceables() {
    Variable x = new Var("x", baseType("oo"));
    ReplaceableList lst = x.freeReplaceables();
    assertTrue(lst.size() == 1);
    assertTrue(lst.contains(x));
    assertTrue(x.boundVars().size() == 0);
  }

  @Test
  public void testTermVarEquality() {
    Term s1 = new Var("x", baseType("o"));
    Term s2 = new Var("x", baseType("o"));
    Term s3 = new Binder("x", baseType("o"));
    assertTrue(s1.equals(s1));
    assertFalse(s1.equals(s2));
    assertFalse(s1.equals(null));
    assertFalse(s1.equals(s3));
    assertFalse(s2.equals(s3));
  }

  @Test
  public void testAlpaEquality() {
    Var x = new Var("x", baseType("o"));
    Var z = new Var("z", baseType("o"));
    TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
    TreeMap<Variable,Integer> xi = new TreeMap<Variable,Integer>();
    assertTrue(x.alphaEquals(x, mu, xi, 2));
    assertFalse(x.alphaEquals(z, mu, xi, 2));
    mu.put(x, 3);
    xi.put(z, 3);
    // only binder variables in mu and xi are considered
    assertFalse(x.alphaEquals(z, mu, xi, 2));
  }

  @Test
  public void testVarOrFunctionalTerm() {
    Term s1 = new Var("x", baseType("o"));
    Term s2 = constantTerm("x", baseType("o"));
    assertFalse(s1.equals(s2));
    assertTrue(s1.toString().equals(s2.toString()));
  }

  @Test
  public void testPositions() {
    Term s = new Var("x", baseType("o"));
    List<Path> lst = s.queryPositions();
    assertTrue(lst.size() == 1);
    assertTrue(lst.get(0).toString().equals("ε"));
    assertTrue(lst.get(0).queryAssociatedTerm() == s);
    assertTrue(lst.get(0).queryCorrespondingSubterm() == s);
    lst = s.queryPositionsForHead((new Var("y", arrowType("o", "o"))).apply(s));
    assertTrue(lst.size() == 0);
    List<HeadPosition> posses = s.queryHeadPositions();
    assertTrue(posses.size() == 1);
    assertTrue(posses.get(0).isPosition());
  }

  @Test
  public void testSubtermGood() {
    Term s = new Var("x", baseType("o"));
    Position p = PositionFactory.empty;
    assertTrue(s.querySubterm(p).equals(s));
    assertTrue(s.querySubterm(new HeadPosition(p)).equals(s));
  }

  @Test(expected = IndexingError.class)
  public void testSubtermBad() {
    Term s = new Var("x", baseType("o"));
    Position p = PositionFactory.createArg(1, PositionFactory.empty);
    Term t = s.querySubterm(p);
  }

  @Test(expected = IndexingError.class)
  public void testHeadSubtermBad() {
    Term s = new Var("x", baseType("o"));
    Position p = PositionFactory.createArg(1, PositionFactory.empty);
    Term t = s.querySubterm(new HeadPosition(p));
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testAbstractionSubtermRequest() {
    Term s = new Var("x", arrowType("o", "O"));
    s.queryAbstractionSubterm();
  }

  @Test
  public void testSubtermReplacementGood() {
    Term s = new Var("x", baseType("a"));
    Term t = twoArgVarTerm();
    Position p = PositionFactory.empty;
    assertTrue(s.replaceSubterm(p, t).equals(t));
    assertTrue(s.replaceSubterm(new HeadPosition(p), t).equals(t));
    assertTrue(s.toString().equals("x"));
  }

  @Test(expected = IndexingError.class)
  public void testSubtermReplacementBad() {
    Term s = new Var("x", baseType("o"));
    Position p = PositionFactory.createArg(1, PositionFactory.empty);
    Term t = s.replaceSubterm(p, twoArgVarTerm());
  }

  @Test(expected = IndexingError.class)
  public void testHeadSubtermReplacementBad() {
    Term s = new Var("x", baseType("o"));
    HeadPosition p = new HeadPosition(PositionFactory.empty, 1);
    Term t = s.replaceSubterm(p, twoArgVarTerm());
  }

  @Test
  public void testSubstituting() {
    Variable x = new Var("x", baseType("Int"));
    Variable y = new Var("y", baseType("Int"));
    Variable z = new Var("z", baseType("Bool"));
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    gamma.extend(y, x); 
    assertTrue(x.substitute(gamma).equals(xterm));
    assertTrue(y.substitute(gamma).equals(x));
    assertTrue(z.substitute(gamma).equals(z));
  }

  @Test
  public void testMatchingNoMappingBinder() {
    Variable x = new Var("x", baseType("a"));
    Term t = twoArgVarTerm();
    Subst gamma = new Subst();
    assertTrue(x.match(t, gamma) == null);
    assertTrue(gamma.get(x).equals(t));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testMatchingNoMappingNonBinder() {
    Variable x = new Var("x", baseType("a"));
    Term t = twoArgVarTerm();
    Subst gamma = new Subst();
    assertTrue(x.match(t, gamma) == null);
    assertTrue(gamma.get(x).equals(t));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testMatchingExistingMapping() {
    Variable x = new Var("x", baseType("a"));
    Term t = twoArgVarTerm();
    Subst gamma = new Subst(x, t);
    assertTrue(x.match(t, gamma) == null);
    assertTrue(gamma.get(x).equals(t));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testMatchingConflictingMapping() {
    Variable x = new Var("x", baseType("a"));
    Term t = twoArgVarTerm();
    Term q = new Var("y", baseType("a"));
    Subst gamma = new Subst(x, q);
    assertTrue(x.match(t, gamma) != null);
    assertTrue(gamma.get(x).equals(q));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testMatchingBadType() {
    Variable x = new Var("x", baseType("a"));
    Term t = constantTerm("u", baseType("b"));
    Subst gamma = new Subst();
    assertTrue(x.match(t, gamma) != null);
  }

  @Test
  public void testRenaming() {
    Variable x = new Var("x", baseType("a"));
    StringBuilder builder = new StringBuilder();
    x.addToString(builder, null);
    builder.append(" ");
    TreeMap<Replaceable,String> map = new TreeMap<Replaceable,String>();
    x.addToString(builder, map, new TreeSet<String>());
    builder.append(" ");
    map.put(x, "y");
    x.addToString(builder, map);
    assertTrue(builder.toString().equals("x x y"));
  }
}

