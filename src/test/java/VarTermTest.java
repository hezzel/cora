/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.exceptions.ArityError;
import cora.exceptions.IndexingError;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.NullCallError;
import cora.exceptions.TypingError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;
import cora.types.*;
import cora.terms.*;
import cora.terms.positions.*;

public class VarTermTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  private Type arrowType(String name1, String name2) {
    return new ArrowType(baseType(name1), baseType(name2));
  }

  private Term constantTerm(String name, Type type) {
    return new UserDefinedSymbol(name, type);
  }

  private Term unaryTerm(String name, Type output, Term arg) {
    Type arrtype = new ArrowType(arg.queryType(), output);
    FunctionSymbol f = new UserDefinedSymbol(name, arrtype);
    return new FunctionalTerm(f, arg);
  }

  private Term twoArgTerm() {
    Type type = new ArrowType(baseType("a"), arrowType("b", "a"));
    Variable x = new Var("x", type);
    Term arg1 = constantTerm("c", baseType("a"));
    Term arg2 = unaryTerm("g", baseType("b"), new Var("y", baseType("b")));
    return new VarTerm(x, arg1, arg2);
  }

  @Test(expected = NullInitialisationError.class)
  public void testUnaryWithNullArg() {
    Variable x = new Var("x", arrowType("a", "b"));
    Term arg = null;
    Term t = new VarTerm(x, arg);
  }

  @Test(expected = NullInitialisationError.class)
  public void testBinaryWithNullSymbol() {
    Term t = new VarTerm(null, constantTerm("a", baseType("b")),
                                      constantTerm("a", baseType("c")));
  }

  @Test(expected = NullInitialisationError.class)
  public void testNullArgs() {
    Variable x = new Var("x", arrowType("a", "b"));
    ArrayList<Term> args = null;
    Term t = new VarTerm(x, args);
  }

  @Test(expected = ArityError.class)
  public void testTooManyArgs() {
    Type type = new ArrowType(baseType("a"), arrowType("b", "a"));
    Variable x = new Var("x", type);
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(constantTerm("c", baseType("a")));
    args.add(constantTerm("d", baseType("b")));
    args.add(constantTerm("e", baseType("a")));
    Term t = new VarTerm(x, args);
  }

  @Test(expected = TypingError.class)
  public void testConstructorBadArgType() {
    Type type = new ArrowType(baseType("a"), arrowType("b", "a"));
    Variable x = new Var("x", type);
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(constantTerm("c", baseType("a")));
    args.add(constantTerm("d", baseType("a")));
    Term t = new VarTerm(x, args);
  }

  @Test(expected = IndexingError.class)
  public void testTooSmallSubterm() {
    Term t = twoArgTerm();
    Term sub = t.queryImmediateSubterm(0);
  }

  @Test(expected = IndexingError.class)
  public void testTooLargeSubterm() {
    Term t = twoArgTerm();
    Term sub = t.queryImmediateSubterm(3);
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testInappropriateRootRequest() {
    Term t = twoArgTerm();
    Term f = t.queryRoot();
  }

  @Test(expected = NullCallError.class)
  public void testNullMatch() {
    Term t = twoArgTerm();
    Substitution subst = new Subst();
    t.match(null, subst);
  }

  @Test
  public void testImmediateSubterms() {
    Term t = twoArgTerm();
    assertTrue(t.numberImmediateSubterms() == 2);
    assertTrue(t.queryImmediateSubterm(1).equals(constantTerm("c", baseType("a"))));
    assertTrue(t.queryImmediateSubterm(2).toString().equals("g(y)"));
  }

  @Test
  public void testVarTermBasics() {
    Term t = twoArgTerm();
    Type type = new ArrowType(baseType("a"), arrowType("b", "a"));
    assertTrue(t.isVarTerm());
    assertFalse(t.isConstant());
    assertFalse(t.isVariable());
    assertFalse(t.isFunctionalTerm());
    assertTrue(t.queryVariable().toString().equals("x"));
    assertTrue(t.queryVariable().queryType().toString().equals("a → b → a"));
    assertTrue(t.toString().equals("x(c, g(y))"));
  }

  @Test
  public void testConstantVarTerm() {
    Variable x = new Var("x", arrowType("b", "a"));
    ArrayList<Term> args = new ArrayList<Term>();
    Term xterm = new VarTerm(x, args);
    assertTrue(xterm.isVariable());
  }

  @Test
  public void testTermEquality() {
    Variable x = new Var("x", baseType("o"));
    Variable y = new Var("y", new ArrowType(baseType("o"), arrowType("o", "o")));
    ArrayList<Term> empty = new ArrayList<Term>();
    Term s1 = x;
    Term s2 = new VarTerm(x, empty);
    Term s3 = y;
    Term s4 = new VarTerm(y, x);
    Term s5 = new VarTerm(y, x, x);
    Term s6 = new VarTerm(y, x, x);
    Term s7 = new VarTerm(y, x, new Var("x", baseType("o")));
    
    assertTrue(s1.equals(s1));
    assertTrue(s1.equals(s2));
    assertFalse(s1.equals(s3));
    assertTrue(s2.equals(s1));
    assertFalse(s3.equals(s4));
    assertFalse(s4.equals(s5));
    assertFalse(s5.equals(s4));
    assertTrue(s5.equals(s6));
    assertFalse(s6.equals(s7));
  }

  @Test
  public void testVars() {
    // let's create: Z(Z(x,c),g(y,x)), where Z, x and y are variables
    Variable z = new Var("Z", new ArrowType(baseType("a"),arrowType("b","a")));
    FunctionSymbol g = new UserDefinedSymbol("g", new ArrowType(baseType("b"),arrowType("a","b")));
    FunctionSymbol c = new UserDefinedSymbol("c", baseType("b"));
    Variable x = new Var("x", baseType("a"));
    Variable y = new Var("y", baseType("b"));
    Term s = new VarTerm(z, new VarTerm(z, x, c), new FunctionalTerm(g, y, x));
    Environment env = s.vars();
    assertTrue(env.contains(x));
    assertTrue(env.contains(y));
    assertTrue(env.contains(z));
    assertTrue(env.size() == 3);
  }

  @Test
  public void testFirstOrder() {
    Variable x = new Var("x", baseType("o"));
    Variable y = new Var("y", arrowType("o", "o"));
    ArrayList<Term> args = new ArrayList<Term>();
    Term x1 = x;
    Term x2 = new VarTerm(x, args);
    Term x3 = y;
    Term x4 = new VarTerm(y, constantTerm("c", baseType("o")));
    assertTrue(x1.queryFirstOrder());
    assertTrue(x2.queryFirstOrder());
    assertFalse(x3.queryFirstOrder());
    assertFalse(x4.queryFirstOrder());
  }

  @Test(expected = ArityError.class)
  public void testApplyingBaseTerm() {
    Term s = twoArgTerm();
    Term t = constantTerm("37", baseType("Int"));
    s.apply(t);
  }

  @Test(expected = TypingError.class)
  public void testApplyingBadType() {
    Type o = baseType("o");
    Type a = baseType("a");
    Type type = new ArrowType(a, new ArrowType(o, a));
    Term c = constantTerm("c", a);
    Variable x = new Var("f", type);
    Term xc = new VarTerm(x, c);
    xc.apply(c);
  }

  @Test
  public void testCorrectApplication() {
    Type o = baseType("o");
    Type a = baseType("a");
    Type type = new ArrowType(a, new ArrowType(o, a));
    Term c = constantTerm("c", a);
    Variable x = new Var("x", type);
    Term xc = new VarTerm(x, c);
    Term xcb = xc.apply(constantTerm("b", o));
    assertTrue(xcb.toString().equals("x(c, b)"));
  }

  @Test
  public void testPositions() {
    Type type = new ArrowType(baseType("a"), arrowType("b", "a"));
    Variable z = new Var("Z", type);
    Term arg1 = unaryTerm("g", baseType("a"), new Var("x", baseType("b")));
    Term arg2 = constantTerm("c", baseType("b"));
    Term term = new VarTerm(z, arg1, arg2);    // Z(g(x),c)
    ArrayList<Position> lst = term.queryAllPositions();
    assertTrue(lst.size() == 4);
    assertTrue(lst.get(0).toString().equals("1.1.ε"));
    assertTrue(lst.get(1).toString().equals("1.ε"));
    assertTrue(lst.get(2).toString().equals("2.ε"));
    assertTrue(lst.get(3).toString().equals("ε"));
  }

  @Test
  public void testSubtermGood() {
    Position p;
    Term s = twoArgTerm();
    p = new EmptyPosition();
    assertTrue(s.querySubterm(p).equals(s));
    p = new ArgumentPosition(1, new EmptyPosition());
    assertTrue(s.querySubterm(p).equals(constantTerm("c", baseType("a"))));
    p = new ArgumentPosition(2, new ArgumentPosition(1, new EmptyPosition()));
    assertTrue(s.querySubterm(p).isVariable());
  }

  @Test(expected = IndexingError.class)
  public void testSubtermBad() {
    Term s = twoArgTerm();
    Position pos = new ArgumentPosition(1, new ArgumentPosition(2, new EmptyPosition()));
    Term t = s.querySubterm(pos);
  }

  @Test
  public void testSubtermReplacementGood() {
    Variable z = new Var("Z", arrowType("Int", "Int"));
    Term s = new VarTerm(z, constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(new ArgumentPosition(1, new EmptyPosition()), s);
    assertTrue(s.toString().equals("Z(37)"));
    assertTrue(t.queryImmediateSubterm(1).equals(s));
    assertTrue(t.toString().equals("Z(Z(37))"));
  }

  @Test(expected = IndexingError.class)
  public void testSubtermReplacementBadPosition() {
    Variable z = new Var("Z", arrowType("Int", "Int"));
    Term s = new VarTerm(z, constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(new ArgumentPosition(2, new EmptyPosition()), s);
  }

  @Test(expected = TypingError.class)
  public void testSubtermReplacementBadType() {
    Variable z = new Var("Z", arrowType("Int", "Bool"));
    Term s = new VarTerm(z, constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(new ArgumentPosition(1, new EmptyPosition()), s);
  }

  @Test
  public void testSubstituting() {
    Variable x = new Var("x", baseType("Int"));
    Variable y = new Var("y", baseType("Int"));
    Variable z = new Var("Z", new ArrowType(baseType("Int"), arrowType("Bool", "Int")));
    Term s = new VarTerm(z, x, unaryTerm("f", baseType("Bool"), y));

    Term thirtyseven = constantTerm("37", baseType("Int"));
    FunctionSymbol g = new UserDefinedSymbol("g", new ArrowType(baseType("o"),
                                new ArrowType(baseType("Int"), arrowType("Bool", "Int"))));
    Term t = new FunctionalTerm(g, constantTerm("c", baseType("o")));

    Substitution gamma = new Subst(x, thirtyseven);
    gamma.extend(y, x);
    gamma.extend(z, t);

    Term q = s.substitute(gamma);
    assertTrue(q.toString().equals("g(c, 37, f(x))"));
  }

  @Test
  public void testBasicMatching() {
    Variable x = new Var("x", baseType("Int"));
    Variable z = new Var("Z", new ArrowType(baseType("Int"), arrowType("Int", "Int")));
    Term three = constantTerm("3", baseType("Int"));
    Term four = constantTerm("4", baseType("Int"));
    Type intintint = new ArrowType(baseType("Int"), arrowType("Int", "Int"));
    FunctionSymbol g = new UserDefinedSymbol("g", intintint);
    FunctionSymbol h = new UserDefinedSymbol("h", new ArrowType(baseType("Int"), intintint));
    Term pattern = new VarTerm(z, three, x);
    Term fx = unaryTerm("f", baseType("Int"), x);
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(fx);
    args.add(three);
    args.add(fx);
    Term s = new FunctionalTerm(h, args);
    Term t = new FunctionalTerm(g, four, three);

    Substitution gamma = pattern.match(s);
    Substitution delta = pattern.match(t);

    assertTrue(gamma != null);
    assertTrue(delta == null);

    assertTrue(gamma.get(x).equals(fx));
    assertTrue(gamma.get(z).equals(new FunctionalTerm(h, fx)));
    assertTrue(gamma.domain().size() == 2);
  }

  @Test
  public void testNonLinearMatching() {
    Variable x = new Var("x", arrowType("o", "o"));
    Term a = constantTerm("a", baseType("o"));
    Term b = constantTerm("b", baseType("o"));
    Type ooo = new ArrowType(baseType("o"), arrowType("o", "o"));
    FunctionSymbol f = new UserDefinedSymbol("f", ooo);
    FunctionSymbol g = new UserDefinedSymbol("g", arrowType("o", "o"));
    FunctionSymbol h = new UserDefinedSymbol("h", ooo);
    Term pattern = new FunctionalTerm(f, new VarTerm(x, a), new VarTerm(x, b));

    Term s = new FunctionalTerm(f, new FunctionalTerm(g, a), new FunctionalTerm(g, b));
    Term t = new FunctionalTerm(f, new FunctionalTerm(h, a, a), new FunctionalTerm(h, a, b));
    Term q = new FunctionalTerm(f, new FunctionalTerm(h, a, a), new FunctionalTerm(h, b, b));
    Term u = new FunctionalTerm(f, a, b);

    Substitution gamma = pattern.match(s);
    assertTrue(gamma != null);
    assertTrue(gamma.get(x).equals(g));

    gamma = new Subst();
    Substitution delta = pattern.match(t);
    assertTrue(delta != null);
    assertTrue(delta.get(x).equals(new FunctionalTerm(h, a)));

    assertTrue(pattern.match(q) == null);
    assertTrue(pattern.match(u) == null);
  }
}
