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

import charlie.types.Type;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;
import java.util.TreeMap;
import java.util.TreeSet;
import charlie.util.Pair;
import charlie.util.NullStorageException;
import charlie.types.TypeFactory;
import charlie.parser.CoraParser;
import charlie.terms.position.*;
import charlie.terms.replaceable.ReplaceableSet;

public class BinderTest {
  private Type type(String desc) { return CoraParser.readType(desc); }

  @Test
  public void testNullName() {
    assertThrows(NullStorageException.class, () -> new Binder(null, type("o")));
  }

  @Test
  public void testNullType() {
    assertThrows(NullStorageException.class, () -> new Binder("x", null));
  }

  @Test
  public void testRootRequest() {
    Variable x = new Binder("x", type("o"));
    assertThrows(InappropriatePatternDataException.class, () -> x.queryRoot());
  }

  @Test
  public void testSubtermRequest() {
    Variable x = new Binder("x", type("o"));
    assertThrows(IndexOutOfBoundsException.class, () -> x.queryArgument(1));
  }

  @Test
  public void testBaseVariableApplication() {
    Term t = new Binder("x", type("Int"));
    assertThrows(TypingException.class, () -> t.apply(t));
  }

  @Test
  public void testIllegalTypeApplication() {
    Term t = new Binder("x", type("a -> b"));
    Term q = new Constant("c", type("b"));
    assertThrows(TypingException.class, () -> t.apply(q));
  }

  @Test
  public void testTermVarBasics() {
    Variable x = new Binder("x", type("o"));
    Variable other = new Binder("x", type("o"));
    Term s = x;
    assertTrue(s.isVariable());
    assertTrue(s.isVarTerm());
    assertFalse(s.isConstant());
    assertFalse(s.isFunctionalTerm());
    assertTrue(s.queryVariable().equals(x));
    assertTrue(s.queryHead().equals(x));
    assertTrue(s.toString().equals("x"));
    assertTrue(s.queryNumberArguments() == 0);
    assertTrue(s.listArguments().isEmpty());
    assertTrue(s.isPattern());
    assertFalse(s.isFirstOrder());
    assertFalse(s.isApplication());
    assertFalse(s.isApplicative());
    assertFalse(s.isClosed());
    assertFalse(s.isGround());
    assertTrue(x.isBinderVariable());
    assertTrue(x.queryIndex() != other.queryIndex());
    Variable z = new Binder("z", type("o -> o"));
    assertFalse(z.isFirstOrder());
    assertFalse(z.isApplicative());
    assertTrue(z.isBinderVariable());
    assertTrue(z.isPattern());
    assertTrue(z.apply(x).equals(new Application(z, x)));
    assertTrue(x.compareTo(x) == 0);
    assertTrue(x.compareTo(z) < 0);
    assertTrue(x.compareTo(new Var("y", type("o"))) > 0);
  }

  @Test
  public void testRefreshBinders() {
    Variable x = new Binder("x", type("o"));
    Variable other = new Binder("x", type("o"));
    TreeMap<Variable,Variable> map = new TreeMap<Variable,Variable>();
    assertTrue(x.renameAndRefreshBinders(map) == x);
    map.put(x, other);
    assertTrue(x.renameAndRefreshBinders(map) == other);
    map.put(x, new Binder("x", type("a")));
    assertThrows(TypingException.class, () -> x.renameAndRefreshBinders(map));
    map.put(other, x);
    Variable y = new Var("y", type("o"));
    map.put(x, y);
    assertTrue(x.renameAndRefreshBinders(map) == y);
  }

  @Test
  public void testHashCode() {
    Variable x = new Binder("x", type("o"));
    Variable other = new Binder("x", type("o"));
    Variable y = new Var("x", type("o"));
    assertTrue(x.hashCode() != other.hashCode());
    assertTrue(x.hashCode() != y.hashCode());
    TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
    mu.put(x, 412);
    mu.put(other, 412);
    assertTrue(x.hashCode(mu) == other.hashCode(mu));
  }

  @Test
  public void testFunctions() {
    FunctionSymbol a = new Constant("a", type("aa"));
    TreeSet<FunctionSymbol> symbols = new TreeSet<FunctionSymbol>();
    Variable x = new Binder("x", type("bb"));
    x.storeFunctionSymbols(symbols);
    assertTrue(symbols.isEmpty());
    symbols.add(a);
    x.storeFunctionSymbols(symbols);
    assertTrue(symbols.size() == 1);
    assertTrue(symbols.contains(a));
  }

  @Test
  public void testTermVarFreeReplaceables() {
    Variable x = new Binder("x", type("oo"));
    ReplaceableSet lst = x.queryFreeReplaceables();
    assertTrue(lst.size() == 1);
    assertTrue(lst.contains(x));
    assertTrue(x.queryBoundVars().size() == 0);
  }

  @Test
  public void testTermVarVars() {
    Variable x = new Binder("x", type("oo"));
    Environment<Variable> vars = x.queryFreeVariables();
    int counter = 0;
    for (Variable v : vars) {
      counter++;
      assertTrue(counter == 1);
      assertTrue(v == x);
    }
  }

  @Test
  public void testTypeVariables() {
    Variable x = new Binder("x", type("oo"));
    assertTrue(x.queryTypeVars().isEmpty());
    Variable y = new Binder("y", type("$alpha -> $beta"));
    assertTrue(y.queryTypeVars().size() == 2);
    assertTrue(y.queryTypeVars().contains(TypeFactory.createVariable("alpha")));
    assertTrue(y.queryTypeVars().contains(TypeFactory.createVariable("beta")));
    assertTrue(y.queryTypeVars() == y.queryTypeVars());
  }

  @Test
  public void testTermVarEquality() {
    Term s1 = new Binder("x", type("o"));
    Term s2 = new Binder("x", type("o"));
    Term s3 = new Var("x", type("o"));
    assertTrue(s1.equals(s1));
    assertFalse(s1.equals(s2));
    assertFalse(s1.equals(null));
    assertFalse(s1.equals(s3));
    assertFalse(s2.equals(s3));
  }

  @Test
  public void testAlphaEquality() {
    Variable x = new Binder("x", type("o"));
    Variable z = new Binder("z", type("o"));
    TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
    TreeMap<Variable,Integer> xi = new TreeMap<Variable,Integer>();
    assertFalse(x.alphaEquals(z, mu, xi, 2));
    mu.put(x, 3);
    assertFalse(x.alphaEquals(z, mu, xi, 4));
    xi.put(z, 3);
    assertTrue(x.alphaEquals(z, mu, xi, 4));
    mu.remove(x);
    assertFalse(x.alphaEquals(z, mu, xi, 4));
    mu.put(x, 2);
    assertFalse(x.alphaEquals(z, mu, xi, 4));
    assertFalse(x.alphaEquals(x, mu, xi, 4));
    assertFalse(z.alphaEquals(z, mu, xi, 4));
    assertTrue(x.alphaEquals(x, xi, xi, 5));
  }

  @Test
  public void testVarOrFunctionalTerm() {
    Term s1 = new Binder("x", type("o"));
    Term s2 = new Constant("x", type("o"));
    assertFalse(s1.equals(s2));
    assertTrue(s1.toString().equals(s2.toString()));
  }

  @Test
  public void testSubterms() {
    Term s = new Binder("x", type("o"));
    List<Pair<Term,Position>> lst = s.listSubterms();
    assertTrue(lst.size() == 1);
    assertTrue(lst.getFirst().fst() == s);
    assertTrue(lst.getFirst().snd().toString().equals("ε"));
  }

  @Test
  public void testPositions() {
    Term s = new Binder("x", type("a -> b"));
    assertTrue(s.listPositions(true).size() == 1);
    assertTrue(s.listPositions(false).size() == 1);
    assertTrue(s.listPositions(false).getFirst().toString().equals("ε"));
  }

  @Test
  public void testSubtermGood() {
    Term s = new Binder("x", type("o"));
    Position p = Position.empty;
    assertTrue(s.querySubterm(p).equals(s));
  }

  @Test
  public void testSubtermBad() {
    Term s = new Binder("x", type("o"));
    Position p = new ArgumentPos(1, Position.empty);
    assertThrows(InvalidPositionException.class, () -> s.querySubterm(p));
  }

  @Test
  public void testHeadSubtermBad() {
    Term s = new Binder("x", type("o"));
    Position p = new FinalPos(1);
    assertThrows(InvalidPositionException.class, () -> s.querySubterm(p));
  }

  @Test
  public void testAbstractionSubtermRequest() {
    Term s = new Binder("x", type("b -> O"));
    assertThrows(InappropriatePatternDataException.class, () -> s.queryAbstractionSubterm());
  }

  @Test
  public void testSubtermReplacementGood() {
    Term s = new Binder("x", type("a"));
    Term t = new Var("y", type("a"));
    Position p = Position.empty;
    assertTrue(s.replaceSubterm(p, t) == t);
    assertTrue(s.toString().equals("x"));
  }

  @Test
  public void testSubtermReplacementBad() {
    Term s = new Binder("x", type("o"));
    Position p = new ArgumentPos(1, Position.empty);
    assertThrows(InvalidPositionException.class,
      () -> s.replaceSubterm(p, new Var("y", type("a"))));
  }

  @Test
  public void testHeadSubtermReplacementBad() {
    Term s = new Binder("x", type("o"));
    Position p = new FinalPos(3);
    assertThrows(InvalidPositionException.class,
      () -> s.replaceSubterm(p, new Constant("g", type("o"))));
  }
}
