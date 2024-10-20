/**************************************************************************************************
 Copyright 2019--2024 Cynthia Kop

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

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeMap;
import charlie.exceptions.*;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.position.*;

public class ConstantTest extends TermTestFoundation {
  @Test
  public void testConstantNullName() {
    assertThrows(NullStorageException.class, () -> new Constant(null, baseType("o")));
  }

  @Test
  public void testConstantEmptyName() {
    assertThrows(IllegalArgumentException.class, () -> new Constant("", baseType("o")));
  }

  @Test
  public void testConstantNullType() {
    assertThrows(NullStorageException.class, () -> new Constant("bing", null));
  }

  @Test
  public void testBaseConstantApply() {
    FunctionSymbol c = new Constant("c", baseType("o"));
    assertThrows(ArityException.class, () -> c.apply(new Constant("a", baseType("o"))));
  }

  @Test
  public void testIllTypedApply() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type c = baseType("c3");
    Type combi = arrowType(a, arrowType(b, c));
    FunctionSymbol f = new Constant("ff", combi);
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(new Constant("aa", a));
    args.add(new Constant("bb", a));
    assertThrows(TypingException.class, () -> f.apply(args));
  }

  @Test
  public void testFunctionSymbolBasics() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type c = baseType("c3");
    Type combi = arrowType(a, arrowType(b, c));
    FunctionSymbol f = new Constant("ff", combi);
    assertTrue(f.queryName().equals("ff"));
    assertTrue(f.toString().equals("ff"));
    assertTrue(f.queryType().equals(combi));
    assertTrue(f.isClosed());
    assertTrue(f.isGround());
    assertFalse(f.isApplication());
    assertTrue(f.isApplicative());
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(new Constant("aa", a));
    args.add(new Constant("bb", b));
    assertTrue(f.apply(args).toString().equals("ff(aa, bb)"));
  }

  @Test
  public void testFunctionSymbolTheory() {
    FunctionSymbol f = new Constant("0", TypeFactory.intSort);
    assertFalse(f.isTheorySymbol());
    assertFalse(f.isTheoryTerm());
    assertFalse(f.isValue());
    assertTrue(f.toValue() == null);
  }

  @Test
  public void testFunctionSymbolEquality() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type c = baseType("c3");
    Type combi = arrowType(a, arrowType(b, c));
    FunctionSymbol f = new Constant("ff", combi);
    FunctionSymbol g = new Constant("ff", combi);
    FunctionSymbol h = new Constant("f", combi);
    FunctionSymbol i = new Constant("f", arrowType(a,c));

    assertTrue(f.equals(g));
    assertTrue(f.hashCode() == g.hashCode());
    assertFalse(f.equals(h));
    assertFalse(f.equals(i));
    assertFalse(f.equals(null));
  }

  @Test
  public void testVariableRequest() {
    Term f = new Constant("f", baseType("a"));
    assertThrows(InappropriatePatternDataException.class, () -> f.queryVariable());
  }

  @Test
  public void testAbstractionSubtermRequest() {
    Constant f = new Constant("a", arrowType("o", "O"));
    assertThrows(InappropriatePatternDataException.class, () -> f.queryAbstractionSubterm());
  }

  @Test
  public void testArgumentPositionRequest() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type combi = arrowType(a, b);
    Constant f = new Constant("f", combi);
    assertThrows(IndexingException.class, () -> f.querySubterm(new ArgumentPos(1, Position.empty)));
  }

  @Test
  public void testPartialPositionRequest() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type combi = arrowType(a, b);
    Constant f = new Constant("f", combi);
    assertThrows(IndexingException.class, () -> f.querySubterm(new FinalPos(1)));
  }

  @Test
  public void testBadPositionReplacement() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type combi = arrowType(a, b);
    Constant f = new Constant("f", combi);
    assertThrows(IndexingException.class, () -> 
      f.replaceSubterm(new LambdaPos(Position.empty), new Constant("a", a)));
  }

  @Test
  public void testBadPartialPositionReplacement() {
    Constant f = new Constant("f", baseType("a"));
    assertThrows(IndexingException.class, () -> 
      f.replaceSubterm(new FinalPos(1), new Constant("a", baseType("a"))));
  }

  @Test
  public void testTermBasics() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type c = baseType("c3");
    Type combi = arrowType(a, arrowType(b, c));
    Term f = new Constant("ff", combi);
    Variable x = new Var("ff", combi);

    assertTrue(f.queryType().equals(combi));
    assertTrue(f.isConstant());
    assertTrue(f.isFunctionalTerm());
    assertFalse(f.isVariable());
    assertFalse(f.isVarTerm());
    assertTrue(f.numberArguments() == 0);
    assertTrue(f.queryArguments().size() == 0);
    assertTrue(f.queryRoot().equals(f));
    assertTrue(f.queryRoot().equals(f));
    assertFalse(f.isFirstOrder());
    assertTrue(f.isPattern());
    assertTrue(f.refreshBinders() == f);
    Subst gamma = new Subst(x, new Constant("gg", combi));
    assertTrue(f.substitute(gamma).equals(f));
    assertTrue(f.freeReplaceables().size() == 0);
    assertTrue(f.boundVars().size() == 0);
    assertTrue(f.hasSubterm(f));
    Term aa = new Constant("g", a);
    assertTrue(aa.isFirstOrder());
    assertTrue(aa.isPattern());
    assertTrue(f.refreshBinders() == f);
    String s = null;
    assertFalse(f.equals(s));
    assertFalse(f.hasSubterm(aa));
  }

  @Test
  public void testTermPositions() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type c = baseType("c3");
    Type combi = arrowType(a, arrowType(b, c));
    Term f = new Constant("ff", combi);
    Variable x = new Var("ff", combi);

    assertTrue(f.querySubterms().size() == 1);
    assertTrue(f.querySubterms().get(0).fst() == f);
    assertTrue(f.querySubterms().get(0).snd().isEmpty());
    assertTrue(f.queryPositions(true).size() == 1);
    assertTrue(f.queryPositions(false).size() == 1);

    assertTrue(f.querySubterm(Position.empty).equals(f));
    assertTrue(f.replaceSubterm(Position.empty, x).equals(x));
  }

  @Test
  public void testTermEquality() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type combi = arrowType(a, b);
    Constant f = new Constant("f", combi);
    Constant g = new Constant("f", combi);
    Constant h = new Constant("h", combi);

    assertTrue(f.equals((Term)f));
    assertTrue(f.equals((Term)g));
    assertFalse(f.equals((Term)h));

    TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
    TreeMap<Variable,Integer> xi = new TreeMap<Variable,Integer>();
    assertTrue(f.alphaEquals(f, mu, xi, 3));
    assertFalse(f.alphaEquals(h, mu, xi, 1));

    ArrayList<Term> args = new ArrayList<Term>();
    args.add(new Constant("aa", a));
    Term fa = new Application(f, args);

    assertFalse(f.equals(fa));
    assertTrue(fa.equals(g.apply(new Constant("aa", a))));

    assertTrue(f.match(g) != null);
  }

  @Test
  public void testEqualsHashCodeConsistent() {
    // Class Object requires
    // https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/lang/Object.html#hashCode()
    // that for all objects o1, o2 for which o1.equals(o2) evaluates to true
    // with method Object::equals(Object), also o1.hashCode() == o2.hashCode()
    // must evaluate to true (classes like HashSet, HashMap, LinkedHashSet,
    // LinkedHashMap rely on this contract). This contract that method
    // hashCode() must be consistent with equals(Object) is inherited by all
    // Java classes.
    Type b = TypeFactory.createSort("b");
    FunctionSymbol a1 = TermFactory.createConstant("a", b);
    FunctionSymbol a2 = TermFactory.createConstant("a", b);
    assertEquals(a1, a2);
    assertEquals(a1.hashCode(), a2.hashCode());
  }

  @Test
  public void testHashSetOfFunctionSymbol() {
    Type b = TypeFactory.createSort("b");
    FunctionSymbol a1 = TermFactory.createConstant("a", b);
    FunctionSymbol a2 = TermFactory.createConstant("a", b);
    assertEquals(a1, a2);
    Set<FunctionSymbol> set = new HashSet<>();
    set.add(a1);
    assertTrue(set.contains(a1));
    assertTrue(set.contains(a2));
  }
}
