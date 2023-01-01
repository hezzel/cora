/**************************************************************************************************
 Copyright 2019, 2022 Cynthia Kop

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
import java.util.ArrayList;
import cora.exceptions.*;
import cora.types.Type;

public class VarTermTest extends TermTestFoundation {
  @Test(expected = NullInitialisationError.class)
  public void testUnaryWithNullArg() {
    Variable x = new Var("x", arrowType("a", "b"), true);
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
    Variable x = new Var("x", arrowType("a", "b"), false);
    List<Term> args = null;
    Term t = new VarTerm(x, args);
  }

  @Test(expected = ArityError.class)
  public void testTooManyArgs() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Variable x = new Var("x", type, true);
    List<Term> args = new ArrayList<Term>();
    args.add(constantTerm("c", baseType("a")));
    args.add(constantTerm("d", baseType("b")));
    args.add(constantTerm("e", baseType("a")));
    Term t = new VarTerm(x, args);
  }

  @Test(expected = TypingError.class)
  public void testConstructorBadArgType() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Variable x = new Var("x", type, false);
    List<Term> args = new ArrayList<Term>();
    args.add(constantTerm("c", baseType("a")));
    args.add(constantTerm("d", baseType("a")));
    Term t = new VarTerm(x, args);
  }

  @Test(expected = IndexingError.class)
  public void testTooSmallSubterm() {
    Term t = twoArgVarTerm();
    Term sub = t.queryArgument(0);
  }

  @Test(expected = IndexingError.class)
  public void testTooLargeSubterm() {
    Term t = twoArgVarTerm();
    Term sub = t.queryArgument(3);
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testInappropriateRootRequest() {
    Term t = twoArgVarTerm();
    Term f = t.queryRoot();
  }

  @Test(expected = NullCallError.class)
  public void testNullMatch() {
    Term t = twoArgVarTerm();
    Substitution subst = new Subst();
    t.match(null, subst);
  }

  @Test
  public void testImmediateSubterms() {
    Term t = twoArgVarTerm();
    assertTrue(t.numberArguments() == 2);
    assertTrue(t.queryArgument(1).equals(constantTerm("c", baseType("a"))));
    assertTrue(t.queryArgument(2).toString().equals("g(y)"));
    List<Term> args = t.queryArguments();
    assertTrue(args.get(0) == t.queryArgument(1));
    assertTrue(args.get(1) == t.queryArgument(2));
    assertTrue(args.size() == 2);
  }

  @Test
  public void testImmediateHeadSubterms() {
    Term t = twoArgVarTerm();
    assertTrue(t.queryImmediateHeadSubterm(0).toString().equals("x"));
    assertTrue(t.queryImmediateHeadSubterm(1).toString().equals("x(c)"));
    assertTrue(t.queryImmediateHeadSubterm(2).toString().equals("x(c, g(y))"));
  }

  @Test
  public void testVarTermBasics() {
    Term t = twoArgVarTerm();
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    assertTrue(t.isVarTerm());
    assertFalse(t.isConstant());
    assertFalse(t.isVariable());
    assertFalse(t.isFunctionalTerm());
    assertFalse(t.isPattern());
    assertTrue(t.isApplication());
    assertTrue(t.queryHead().equals(t.queryVariable()));
    assertTrue(t.queryVariable().toString().equals("x"));
    assertTrue(t.queryVariable().queryType().toString().equals("a ⇒ b ⇒ a"));
    assertTrue(t.toString().equals("x(c, g(y))"));
  }

  @Test
  public void testConstantVarTerm() {
    Variable x = new Var("x", arrowType("b", "a"), true);
    List<Term> args = new ArrayList<Term>();
    Term xterm = new VarTerm(x, args);
    assertTrue(xterm.isVariable());
    assertTrue(xterm.isPattern());
    assertFalse(xterm.isApplication());
  }

  @Test
  public void testBinderPattern() {
    Variable x = new Var("x", arrowType(baseType("b"), arrowType("b", "a")), true);
    Variable y = new Var("y", baseType("b"), false);
    Variable z = new Var("z", arrowType("b", "b"), false);
    Constant bb = new Constant("bb", baseType("b"));
    List<Term> args = new ArrayList<Term>();
    args.add(y);
    args.add(bb);
    Term xybterm = new VarTerm(x, args);
    assertTrue(xybterm.isPattern());    // we're allowed to apply binder variables
    args.set(1, z.apply(bb));
    Term combiterm = new VarTerm(x, args);
    assertFalse(combiterm.isPattern()); // but the arguments do all need to be patterns :)
  }

  @Test
  public void testTermEquality() {
    Variable x = new Var("x", baseType("o"), false);
    Variable y = new Var("y", arrowType(baseType("o"), arrowType("o", "o")), false);
    List<Term> empty = new ArrayList<Term>();
    Term s1 = x;
    Term s2 = new VarTerm(x, empty);
    Term s3 = y;
    Term s4 = new VarTerm(y, x);
    Term s5 = new VarTerm(y, x, x);
    Term s6 = new VarTerm(y, x, x);
    Term s7 = new VarTerm(y, x, new Var("x", baseType("o"), false));
    
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
    Variable z = new Var("Z", arrowType(baseType("a"),arrowType("b","a")), true);
    FunctionSymbol g = new Constant("g", arrowType(baseType("b"),arrowType("a","b")));
    FunctionSymbol c = new Constant("c", baseType("b"));
    Variable x = new Var("x", baseType("a"), true);
    Variable y = new Var("y", baseType("b"), false);
    Term s = new VarTerm(z, new VarTerm(z, x, c), new FunctionalTerm(g, y, x));
    Environment env = s.vars();
    assertTrue(env.contains(x));
    assertTrue(env.contains(y));
    assertTrue(env.contains(z));
    assertTrue(env.size() == 3);
  }

  @Test
  public void testFirstOrder() {
    Variable x = new Var("x", baseType("o"), false);
    Variable y = new Var("y", arrowType("o", "o"), false);
    Variable z = new Var("x", baseType("o"), true);
    List<Term> args = new ArrayList<Term>();
    Term x1 = x;
    Term x2 = new VarTerm(x, args);
    Term x3 = y;
    Term x4 = new VarTerm(y, constantTerm("c", baseType("o")));
    Term x5 = new VarTerm(z, args);
    assertTrue(x1.isFirstOrder());
    assertTrue(x2.isFirstOrder());
    assertFalse(x3.isFirstOrder());
    assertFalse(x4.isFirstOrder());
    assertFalse(x5.isFirstOrder());
  }

  @Test(expected = ArityError.class)
  public void testApplyingBaseTerm() {
    Term s = twoArgVarTerm();
    Term t = constantTerm("37", baseType("Int"));
    s.apply(t);
  }

  @Test(expected = TypingError.class)
  public void testApplyingBadType() {
    Type o = baseType("o");
    Type a = baseType("a");
    Type type = arrowType(a, arrowType(o, a));
    Term c = constantTerm("c", a);
    Variable x = new Var("f", type, false);
    Term xc = new VarTerm(x, c);
    xc.apply(c);
  }

  @Test
  public void testCorrectApplication() {
    Type o = baseType("o");
    Type a = baseType("a");
    Type type = arrowType(a, arrowType(o, a));
    Term c = constantTerm("c", a);
    Variable x = new Var("x", type, false);
    Term xc = new VarTerm(x, c);
    Term xcb = xc.apply(constantTerm("b", o));
    assertTrue(xcb.toString().equals("x(c, b)"));
  }

  @Test
  public void testPositions() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Variable z = new Var("Z", type, true);
    Term arg1 = unaryTerm("g", baseType("a"), new Var("x", baseType("b"), false));
    Term arg2 = constantTerm("c", baseType("b"));
    Term term = new VarTerm(z, arg1, arg2);    // Z(g(x),c)
    List<Position> lst = term.queryAllPositions();
    assertTrue(lst.size() == 4);
    assertTrue(lst.get(0).toString().equals("1.1.ε"));
    assertTrue(lst.get(1).toString().equals("1.ε"));
    assertTrue(lst.get(2).toString().equals("2.ε"));
    assertTrue(lst.get(3).toString().equals("ε"));
  }

  @Test
  public void testSubtermGood() {
    Position p;
    Term s = twoArgVarTerm();
    p = PositionFactory.empty;
    assertTrue(s.querySubterm(p).equals(s));
    p = new ArgumentPosition(1, PositionFactory.empty);
    assertTrue(s.querySubterm(p).equals(constantTerm("c", baseType("a"))));
    p = new ArgumentPosition(2, new ArgumentPosition(1, PositionFactory.empty));
    assertTrue(s.querySubterm(p).isVariable());
  }

  @Test(expected = IndexingError.class)
  public void testSubtermBad() {
    Term s = twoArgVarTerm();
    Position pos = new ArgumentPosition(1, new ArgumentPosition(2, PositionFactory.empty));
    Term t = s.querySubterm(pos);
  }

  @Test
  public void testSubtermReplacementGood() {
    Variable z = new Var("Z", arrowType("Int", "Int"), false);
    Term s = new VarTerm(z, constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(new ArgumentPosition(1, PositionFactory.empty), s);
    assertTrue(s.toString().equals("Z(37)"));
    assertTrue(t.queryArgument(1).equals(s));
    assertTrue(t.toString().equals("Z(Z(37))"));
  }

  @Test(expected = IndexingError.class)
  public void testSubtermReplacementBadPosition() {
    Variable z = new Var("Z", arrowType("Int", "Int"), false);
    Term s = new VarTerm(z, constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(new ArgumentPosition(2, PositionFactory.empty), s);
  }

  @Test(expected = TypingError.class)
  public void testSubtermReplacementBadTypeSub() {
    Variable z = new Var("Z", arrowType("Int", "Bool"), false);
    Term s = new VarTerm(z, constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(new ArgumentPosition(1, PositionFactory.empty), s);
  }

  @Test(expected = TypingError.class)
  public void testSubtermReplacementBadTypeTop() {
    Variable z = new Var("Z", arrowType("Int", "Bool"), true);
    Term s = new VarTerm(z, constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(PositionFactory.empty, constantTerm("42", baseType("Int")));
  }

  @Test
  public void testSubstituting() {
    Variable x = new Var("x", baseType("Int"), true);
    Variable y = new Var("y", baseType("Int"), false);
    Variable z = new Var("Z", arrowType(baseType("Int"), arrowType("Bool", "Int")), false);
    Term s = new VarTerm(z, x, unaryTerm("f", baseType("Bool"), y));

    Term thirtyseven = constantTerm("37", baseType("Int"));
    FunctionSymbol g = new Constant("g", arrowType(baseType("o"),
                                         arrowType(baseType("Int"), arrowType("Bool", "Int"))));
    Term t = new FunctionalTerm(g, constantTerm("c", baseType("o")));

    Substitution gamma = new Subst(x, thirtyseven);
    gamma.extend(y, x);
    gamma.extend(z, t);

    Term q = s.substitute(gamma);
    assertTrue(q.toString().equals("g(c, 37, f(x))"));
  }

  @Test
  public void testBasicMatching() {
    Variable x = new Var("x", baseType("Int"), true);
    Variable z = new Var("Z", arrowType(baseType("Int"), arrowType("Int", "Int")), true);
    Term three = constantTerm("3", baseType("Int"));
    Term four = constantTerm("4", baseType("Int"));
    Type intintint = arrowType(baseType("Int"), arrowType("Int", "Int"));
    FunctionSymbol g = new Constant("g", intintint);
    FunctionSymbol h = new Constant("h", arrowType(baseType("Int"), intintint));
    Term pattern = new VarTerm(z, three, x);
    Term fx = unaryTerm("f", baseType("Int"), x);
    List<Term> args = new ArrayList<Term>();
    args.add(fx);
    args.add(three);
    args.add(fx);
    Term s = new FunctionalTerm(h, args);
    Term t = new FunctionalTerm(g, four, three);

    // Z(3, x) is asked to match with h(f(x), 3, f(x))
    // This should map Z to h(f(x)) and x to f(x)
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
    Variable x = new Var("x", arrowType("o", "o"), true);
    Term a = constantTerm("a", baseType("o"));
    Term b = constantTerm("b", baseType("o"));
    Type ooo = arrowType(baseType("o"), arrowType("o", "o"));
    FunctionSymbol f = new Constant("f", ooo);
    FunctionSymbol g = new Constant("g", arrowType("o", "o"));
    FunctionSymbol h = new Constant("h", ooo);
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
