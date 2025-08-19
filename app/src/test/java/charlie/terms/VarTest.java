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

package charlie.terms;

import java.util.List;
import java.util.TreeMap;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import charlie.util.Pair;
import charlie.util.NullStorageException;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.position.*;
import charlie.terms.replaceable.ReplaceableList;

public class VarTest extends TermTestFoundation {
  @Test
  public void testNullInitialisation() {
    assertThrows(NullStorageException.class, () -> new Var(null, baseType("o")));
    assertThrows(NullStorageException.class, () -> new Var("x", null));
  }

  @Test
  public void testRootRequest() {
    Variable x = new Var("x", baseType("o"));
    assertThrows(InappropriatePatternDataException.class, () -> x.queryRoot());
  }

  @Test
  public void testSubtermRequest() {
    Variable x = new Var("x", baseType("o"));
    assertThrows(IndexOutOfBoundsException.class, () -> x.queryArgument(1));
  }

  @Test
  public void testNullSubstitution() {
    Term t = new Var("x", baseType("Int"));
    assertThrows(NullPointerException.class, () -> t.substitute(null));
  }

  @Test
  public void testNullMatch1() {
    Term t = new Var("x", baseType("Int"));
    assertThrows(NullPointerException.class,
      () -> t.match(constantTerm("37", baseType("Int")), null));
  }

  @Test
  public void testNullMatch2() {
    Term t = new Var("x", baseType("Int"));
    Substitution subst = new Subst();
    assertThrows(NullPointerException.class, () -> t.match(null, subst));
  }

  @Test
  public void testBaseVariableApplication() {
    Term t = new Var("x", baseType("Int"));
    assertThrows(TypingException.class, () -> t.apply(t)); }
  @Test
  public void testIllegalTypeApplication() {
    Term t = new Var("x", arrowType("a", "b"));
    Term q = constantTerm("c", baseType("b"));
    assertThrows(TypingException.class, () -> t.apply(q));
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
    assertTrue(s.isLinear());
    Variable y = new Binder("x", baseType("o"));
    assertTrue(x.compareTo(y) == -1);
  }

  @Test
  public void testTheory() {
    Variable x = new Var("x", baseType("aa"));
    Variable y = new Var("y", arrowType(TypeFactory.intSort, TypeFactory.stringSort));
    assertFalse(x.isTheoryTerm());
    assertTrue(y.isTheoryTerm());
    assertFalse(y.isValue());
    assertTrue(y.toValue() == null);
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
    Var x = new Var("x", baseType("o"));
    Term s1 = x;
    Term s2 = new Var("x", baseType("o"));
    Term s3 = new Binder("x", baseType("o"));
    assertTrue(s1.equals(s1));
    assertFalse(s1.equals(s2));
    assertFalse(s1.equals(null));
    assertFalse(s1.equals(s3));
    assertFalse(s2.equals(s3));
    assertTrue(s1.hashCode() != s2.hashCode());
    TreeMap<Variable,Integer> map = new TreeMap<Variable,Integer>();
    map.put(x, s3.queryVariable().queryIndex());
    assertTrue(s1.hashCode(map) != s3.hashCode(map));
  }

  @Test
  public void testAlphaEquality() {
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
  public void testSubterms() {
    Term s = new Var("x", baseType("o"));
    List<Pair<Term,Position>> lst = s.querySubterms();
    assertTrue(lst.size() == 1);
    assertTrue(lst.get(0).fst() == s);
    assertTrue(lst.get(0).snd().toString().equals("ε"));
  }

  @Test
  public void testPositions() {
    Term s = new Var("x", baseType("o"));
    List<Position> posses = s.queryPositions(true);
    assertTrue(posses.size() == 1);
    assertTrue(posses.get(0).isEmpty());
  }

  @Test
  public void testSubtermGood() {
    Term s = new Var("x", baseType("o"));
    Position p = Position.empty;
    assertTrue(s.querySubterm(p).equals(s));
  }

  @Test
  public void testSubtermBad() {
    Term s = new Var("x", baseType("o"));
    Position p = new ArgumentPos(1, Position.empty);
    assertThrows(InvalidPositionException.class, () -> s.querySubterm(p));
  }

  @Test
  public void testHeadSubtermBad() {
    Term s = new Var("x", baseType("o"));
    Position p = new ArgumentPos(1, Position.empty);
    assertThrows(InvalidPositionException.class, () -> s.querySubterm(p));
  }

  @Test
  public void testAbstractionSubtermRequest() {
    Term s = new Var("x", arrowType("o", "O"));
    assertThrows(InappropriatePatternDataException.class, () -> s.queryAbstractionSubterm());
  }

  @Test
  public void testSubtermReplacementGood() {
    Term s = new Var("x", baseType("a"));
    Term t = twoArgVarTerm();
    Position p = Position.empty;
    assertTrue(s.replaceSubterm(p, t).equals(t));
    assertTrue(s.toString().equals("x"));
  }

  @Test
  public void testSubtermReplacementBad() {
    Term s = new Var("x", baseType("o"));
    Position p = new MetaPos(1, Position.empty);
    assertThrows(InvalidPositionException.class, () -> s.replaceSubterm(p, twoArgVarTerm()));
  }

  @Test
  public void testHeadSubtermReplacementBad() {
    Term s = new Var("x", baseType("o"));
    Position p = new FinalPos(1);
    assertThrows(InvalidPositionException.class, () -> s.replaceSubterm(p, twoArgVarTerm()));
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
}

