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

package charlie.terms;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeMap;
import charlie.util.NullStorageException;
import charlie.types.Type;
import charlie.types.TVar;
import charlie.types.TypeFactory;
import charlie.types.TestSubstitution;
import charlie.parser.CoraParser;
import charlie.terms.position.*;

public class ConstantTest  {
  private Type type(String desc) { return CoraParser.readType(desc); }

  @Test
  public void testConstantNullName() {
    assertThrows(NullStorageException.class, () -> new Constant(null, type("o")));
  }

  @Test
  public void testConstantEmptyName() {
    assertThrows(IllegalArgumentException.class, () -> new Constant("", type("o")));
  }

  @Test
  public void testConstantNullType() {
    assertThrows(NullStorageException.class, () -> new Constant("bing", null));
  }

  @Test
  public void testBaseConstantApply() {
    FunctionSymbol c = new Constant("c", type("o"));
    assertThrows(TypingException.class, () -> c.apply(new Constant("a", type("o"))));
  }

  @Test
  public void testIllTypedApply() {
    FunctionSymbol f = new Constant("ff", type("a -> b -> c"));
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(new Constant("aa", type("a")));
    args.add(new Constant("bb", type("a")));
    assertThrows(TypingException.class, () -> f.apply(args));
  }

  @Test
  public void testFunctionSymbolBasics() {
    Type abc = type("a -> b -> c3");
    FunctionSymbol f = new Constant("ff", abc);
    assertTrue(f.queryName().equals("ff"));
    assertTrue(f.toString().equals("ff"));
    assertTrue(f.queryType().equals(abc));
    assertTrue(f.isClosed());
    assertTrue(f.isGround());
    assertFalse(f.isApplication());
    assertTrue(f.isApplicative());
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(new Constant("aa", type("a")));
    args.add(new Constant("bb", type("b")));
    assertTrue(f.apply(args).toString().equals("ff(aa, bb)"));
  }

  @Test
  public void testFunctionSymbolEquality() {
    Type abc = type("a -> b -> c");
    FunctionSymbol f = new Constant("ff", abc);
    FunctionSymbol g = new Constant("ff", abc);
    FunctionSymbol h = new Constant("f", abc);
    FunctionSymbol i = new Constant("f", type("a -> c"));

    assertTrue(f.equals(g));
    assertTrue(f.hashCode() == g.hashCode());
    assertFalse(f.equals(h));
    assertFalse(f.equals(i));
    assertFalse(f.equals(null));
  }

  @Test
  public void testVariableRequest() {
    Term f = new Constant("f", type("a"));
    assertThrows(InappropriatePatternDataException.class, () -> f.queryVariable());
  }

  @Test
  public void testAbstractionSubtermRequest() {
    Constant f = new Constant("a", type("o -> O"));
    assertThrows(InappropriatePatternDataException.class, () -> f.queryAbstractionSubterm());
  }

  @Test
  public void testArgumentPositionRequest() {
    Constant f = new Constant("f", type("a -> b"));
    assertThrows(InvalidPositionException.class, () ->
      f.querySubterm(new ArgumentPos(1, Position.empty)));
  }

  @Test
  public void testPartialPositionRequest() {
    Constant f = new Constant("f", type("a -> b"));
    assertThrows(InvalidPositionException.class, () ->
      f.querySubterm(new FinalPos(1)));
  }

  @Test
  public void testBadPositionReplacement() {
    Constant f = new Constant("f", type("a -> b"));
    assertThrows(InvalidPositionException.class, () -> 
      f.replaceSubterm(new LambdaPos(Position.empty), new Constant("a", type("a"))));
  }

  @Test
  public void testBadPartialPositionReplacement() {
    Constant f = new Constant("f", type("a"));
    assertThrows(InvalidPositionException.class, () -> 
      f.replaceSubterm(new FinalPos(1), new Constant("a", type("a"))));
  }

  @Test
  public void testTermBasics() {
    Type abc = type("a -> $b -> c");
    Term f = new Constant("ff", abc);
    Variable x = new Var("ff", abc);

    assertTrue(f.queryType().equals(abc));
    assertTrue(f.isConstant());
    assertTrue(f.isFunctionalTerm());
    assertFalse(f.isVariable());
    assertFalse(f.isVarTerm());
    assertTrue(f.queryNumberArguments() == 0);
    assertTrue(f.listArguments().isEmpty());
    assertTrue(f.queryRoot().equals(f));
    assertTrue(f.queryRoot().equals(f));
    assertFalse(f.isFirstOrder());
    assertTrue(f.isPattern());
    assertTrue(f.renameAndRefreshBinders(new TreeMap<Variable,Variable>()) == f);
    assertTrue(f.queryFreeReplaceables().size() == 0);
    assertTrue(f.queryBoundVars().size() == 0);
    assertTrue(f.queryTypeVars().size() == 1);
    assertTrue(f.hasSubterm(f));
    Term aa = new Constant("g", type("a"));
    assertTrue(aa.isFirstOrder());
    assertTrue(aa.isPattern());
    String s = null;
    assertFalse(f.equals(x));
    assertFalse(f.equals(s));
    assertFalse(f.hasSubterm(aa));
  }

  @Test
  public void testTermPositions() {
    Type abc = type("a -> b -> c");
    Term f = new Constant("ff", abc);
    Variable x = new Var("ff", abc);

    var subs = f.listSubterms();
    assertTrue(subs.size() == 1);
    assertTrue(subs.getFirst().fst() == f);
    assertTrue(subs.getFirst().snd().isEmpty());
    assertTrue(f.listPositions(true).size() == 1);
    assertTrue(f.listPositions(false).size() == 1);

    assertTrue(f.querySubterm(Position.empty).equals(f));
    assertTrue(f.replaceSubterm(Position.empty, x).equals(x));
  }

  @Test
  public void testTermEquality() {
    Type ab = type("a -> b");
    Constant f = new Constant("f", ab);
    Constant g = new Constant("f", ab);
    Constant h = new Constant("h", ab);
    Constant i = new Constant("i", type("a -> c"));

    assertTrue(f.equals((Term)f));
    assertTrue(f.equals((Term)g));
    assertFalse(f.equals((Term)h));
    assertFalse(f.equals((Term)i));

    TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
    TreeMap<Variable,Integer> xi = new TreeMap<Variable,Integer>();
    assertTrue(f.alphaEquals(f, mu, xi, 3));
    assertFalse(f.alphaEquals(h, mu, xi, 1));

    ArrayList<Term> args = new ArrayList<Term>();
    args.add(new Constant("aa", type("a")));
    Term fa = new Application(f, args);

    assertFalse(f.equals(fa));
    assertTrue(fa.equals(g.apply(new Constant("aa", type("a")))));
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
    FunctionSymbol a1 = TermFactory.createConstant("a", type("b"));
    FunctionSymbol a2 = TermFactory.createConstant("a", type("b"));
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

  @Test
  public void testSubstituteTypes() {
    // create f_{α → c(β, Int)}
    TVar beta = TypeFactory.createVariable("β");
    Type tuple = TypeFactory.createSort("c", beta, TypeFactory.intSort);
    Type mytype = TypeFactory.createArrow(TypeFactory.createVariable("α"), tuple);
    FunctionSymbol f = TermFactory.createConstant("f", mytype);
    // create [β := c(β,β)]
    TestSubstitution map = new TestSubstitution();
    map.extend(beta, TypeFactory.createSort("c", beta, beta));
    // substitute!
    FunctionSymbol g = f.substituteType(map);
    assertTrue(f.queryType() == mytype);
    assertTrue(g.queryType().toString().equals("$α → c(c($β, $β), Int)"));
  }

  @Test
  public void testMatch() {
    TVar alpha = TypeFactory.createVariable("alpha");
    TVar beta = TypeFactory.createVariable("beta");
    TVar eta = TypeFactory.createVariable("eta");
    Type it = TypeFactory.intSort;
    Type itb = TypeFactory.createArrow(TypeFactory.boolSort, it);
    Type ab = TypeFactory.createArrow(alpha, beta);
    Type result = TypeFactory.createArrow(it, itb);
    FunctionSymbol f1 = TermFactory.createConstant("f", ab);
    FunctionSymbol f2 = TermFactory.createConstant("f", result);
    FunctionSymbol g1 = TermFactory.createConstant("g", eta);

    // empty substitution: f1 match against f2
    TestSubstitution subst = new TestSubstitution();
    assertTrue(f1.match(f2, subst));
    assertTrue(subst.size() == 2); 
    assertTrue(subst.get(alpha).equals(it));
    assertTrue(subst.get(beta).equals(itb));

    // empty substitution: g1 match against f2
    subst = new TestSubstitution();
    assertFalse(g1.match(f2, subst));
    assertTrue(subst.size() == 0); 
    assertTrue(subst.get(eta) == null);

    // non-empty substitution: f1 match successfully against f2
    subst = new TestSubstitution();
    subst.extend(alpha, it);
    assertTrue(f1.match(f2, subst));
    assertTrue(subst.size() == 2); 
    assertTrue(subst.get(alpha).equals(it));
    assertTrue(subst.get(beta).equals(itb));

    // non-empty substitution where variables are set to that f1 does not match against f2
    subst = new TestSubstitution();
    subst.extend(beta, it);
    assertFalse(f1.match(f2, subst));
    assertTrue(subst.size() <= 2); 
    assertTrue(subst.get(beta).equals(it));
  }
}
