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
import java.util.ArrayList;
import cora.exceptions.*;
import cora.types.Type;

public class ApplicationTest extends TermTestFoundation {
  @Test(expected = NullInitialisationError.class)
  public void testUnaryWithNullArg() {
    Variable head = new Var("x", arrowType("a", "b"), true);
    Term arg = null;
    Term t = new Application(head, arg);
  }

  @Test(expected = NullInitialisationError.class)
  public void testBinaryWithNullHead() {
    Term t = new Application(null, constantTerm("a", baseType("b")),
                                   constantTerm("a", baseType("c")));
  }

  @Test(expected = NullInitialisationError.class)
  public void testNullArgs() {
    Constant f = new Constant("f", arrowType("a", "b"));
    List<Term> args = null;
    Term t = new Application(f, args);
  }

  @Test(expected = ArityError.class)
  public void testTooManyArgs() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Variable x = new Var("x", type, true);
    List<Term> args = new ArrayList<Term>();
    args.add(constantTerm("c", baseType("a")));
    args.add(constantTerm("d", baseType("b")));
    args.add(constantTerm("e", baseType("a")));
    Term t = new Application(x, args);
  }

  @Test(expected = ArityError.class)
  public void testTooManyArgsToApplication() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Variable x = new Var("x", type, true);
    Term head = x.apply(constantTerm("c", baseType("a")));
    List<Term> args = new ArrayList<Term>();
    args.add(constantTerm("d", baseType("b")));
    args.add(constantTerm("e", baseType("a")));
    Term t = new Application(head, args);
  }

  @Test(expected = TypingError.class)
  public void testConstructorBadArgType() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Term head = constantTerm("f", type);
    List<Term> args = new ArrayList<Term>();
    args.add(constantTerm("c", baseType("a")));
    args.add(constantTerm("d", baseType("a")));
    Term t = new Application(head, args);
  }

  @Test(expected = TypingError.class)
  public void testConstructorBadArgTypeToApplication() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Term head = constantTerm("f", type).apply(constantTerm("c", baseType("a")));
    Term t = new Application(head, constantTerm("d", baseType("a")));
  }

  @Test(expected = IllegalArgumentError.class)
  public void testCreateEmptyApplication() {
    Term head = new Var("x", arrowType(baseType("a"), arrowType("b", "a")), false);
    List<Term> args = new ArrayList<Term>();
    Application appl = new Application(head, args);
  }

  @Test
  public void testConstructApplicationFromApplicationHead() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Term head = constantTerm("f", type).apply(constantTerm("c", baseType("a")));
    Term t = new Application(head, constantTerm("d", baseType("b")));
    assertTrue(t.toString().equals("f(c, d)"));
    assertTrue(t.queryType().equals(baseType("a")));

    Term s = new Application(t, new ArrayList<Term>());
    assertTrue(s.equals(t));
  }

  @Test
  public void testFunctionalTermBasics() {
    Term t = twoArgFuncTerm();
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    assertTrue(t.isApplication());
    assertTrue(t.isFunctionalTerm());
    assertFalse(t.isConstant());
    assertFalse(t.isVariable());
    assertFalse(t.isVarTerm());
    assertTrue(t.isPattern());
    assertTrue(t.isApplication());
    assertTrue(t.queryRoot().equals(new Constant("f", type)));
    assertTrue(t.queryHead().equals(t.queryRoot()));
    assertTrue(t.queryHead().queryType().toString().equals("a ⇒ b ⇒ a"));
    assertTrue(t.queryType().equals(baseType("a")));
    assertTrue(t.toString().equals("f(c, g(d))"));
  }

  @Test
  public void testVarTermBasics() {
    Term t = twoArgVarTerm();
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    assertTrue(t.isApplication());
    assertTrue(t.isVarTerm());
    assertFalse(t.isConstant());
    assertFalse(t.isVariable());
    assertFalse(t.isFunctionalTerm());
    assertFalse(t.isPattern());
    assertTrue(t.isApplication());
    assertTrue(t.queryVariable().toString().equals("x"));
    assertTrue(t.queryHead().equals(t.queryVariable()));
    assertTrue(t.queryHead().queryType().toString().equals("a ⇒ b ⇒ a"));
    assertTrue(t.queryType().equals(baseType("a")));
    assertTrue(t.toString().equals("x(c, g(y))"));
  }

  @Test(expected = IndexingError.class)
  public void testTooSmallSubterm() {
    Term t = twoArgVarTerm();
    Term sub = t.queryArgument(0);
  }

  @Test(expected = IndexingError.class)
  public void testTooLargeSubterm() {
    Term t = twoArgFuncTerm();
    Term sub = t.queryArgument(3);
  }

  @Test
  public void testArguments() {
    Term t = twoArgFuncTerm();
    assertTrue(t.numberArguments() == 2);
    assertTrue(t.queryArgument(1).equals(constantTerm("c", baseType("a"))));
    assertTrue(t.queryArgument(2).toString().equals("g(d)"));
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

  @Test(expected = InappropriatePatternDataError.class)
  public void testInappropriateRootRequest() {
    Term t = twoArgVarTerm();
    Term f = t.queryRoot();
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testInappropriateVariableRequest() {
    Term t = twoArgFuncTerm();
    Term f = t.queryVariable();
  }

  @Test
  public void testFirstOrderFunctionalTerm() {
    Type aa = arrowType("a", "a");
    Term s = twoArgFuncTerm();
    Term t = unaryTerm("h", aa, new Var("x", baseType("b"), false));
    Type utype = arrowType(baseType("a"), arrowType(aa, baseType("b")));
    Term q = new Application(new Constant("u", utype), s, t); 
    assertTrue(s.isFirstOrder());
    assertFalse(t.isFirstOrder());
    assertFalse(q.isFirstOrder());
  }

  @Test
  public void testFirstOrderVarTerm() {
    Variable y = new Var("y", arrowType("o", "o"), true);
    Term x3 = new Application(y, constantTerm("c", baseType("o")));
    assertFalse(x3.isFirstOrder());
  }

  @Test
  public void testNonPattern() {
    Var x = new Var("x", arrowType("A", "B"), false);
    Term xa = new Application(x, constantTerm("a", baseType("A")));
    Term f = new Constant("f", arrowType("B", "B"));
    Term fxa = new Application(f, xa);
    assertFalse(fxa.isPattern());
  }

  @Test
  public void testBinderPattern() {
    Variable x = new Var("x", arrowType(baseType("b"), arrowType("b", "a")), true);
    Variable y = new Var("y", baseType("b"), false);
    Variable z = new Var("z", arrowType("b", "b"), false);
    Term ba = new Constant("bb", arrowType("a", "b")).apply(constantTerm("aa", baseType("a")));
    List<Term> args = new ArrayList<Term>();
    args.add(y);
    args.add(ba);
    Term xybterm = new Application(x, args);  // x(y, bb(aa))
    assertTrue(xybterm.isPattern());    // we're allowed to apply binder variables
    args.set(1, z.apply(ba));
    Term combiterm = new Application(x, args);  // x(y, bb(aa), z(bb(aa)))
    assertFalse(combiterm.isPattern()); // but the arguments do all need to be patterns :)
  }

  @Test
  public void testPositions() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Variable z = new Var("Z", type, true);
    Term arg1 = unaryTerm("g", baseType("a"), new Var("x", baseType("b"), false));
    Term arg2 = constantTerm("c", baseType("b"));
    Term term = new Application(z, arg1, arg2);    // Z(g(x),c)
    List<Path> lst = term.queryPositions();
    assertTrue(lst.size() == 4);
    assertTrue(lst.get(0).toString().equals("1.1.ε"));
    assertTrue(lst.get(1).toString().equals("1.ε"));
    assertTrue(lst.get(2).toString().equals("2.ε"));
    assertTrue(lst.get(3).toString().equals("ε"));
    assertTrue(lst.get(1).queryAssociatedTerm() == term);
    assertTrue(lst.get(2).queryCorrespondingSubterm() == term.queryArgument(2));
    assertTrue(lst.get(3).queryCorrespondingSubterm() == term);
  }

  @Test
  public void testHeadPositions() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Variable z = new Var("Z", type, true);
    Term arg1 = unaryTerm("g", baseType("a"), new Var("x", baseType("b"), false));
    Term arg2 = constantTerm("c", baseType("b"));
    Term term = new Application(z, arg1, arg2);    // Z(g(x),c)
    List<HeadPosition> lst = term.queryHeadPositions();
    assertTrue(lst.size() == 7);
    assertTrue(lst.get(0).toString().equals("1.1.ε"));
    assertTrue(lst.get(1).toString().equals("1.☆1"));
    assertTrue(lst.get(2).toString().equals("1.ε"));
    assertTrue(lst.get(3).toString().equals("2.ε"));
    assertTrue(lst.get(4).toString().equals("☆2"));
    assertTrue(lst.get(5).toString().equals("☆1"));
    assertTrue(lst.get(6).toString().equals("ε"));
  }

  @Test
  public void testVars() {
    // let's create: Z(Z(x,c),g(y,x)), where Z, x and y are variables
    Variable z = new Var("Z", arrowType(baseType("a"),arrowType("b","a")), true);
    FunctionSymbol g = new Constant("g", arrowType(baseType("b"),arrowType("a","b")));
    FunctionSymbol c = new Constant("c", baseType("b"));
    Variable x = new Var("x", baseType("a"), true);
    Variable y = new Var("y", baseType("b"), false);
    Term s = new Application(z, new Application(z, x, c), new Application(g, y, x));
    VariableList lst = s.vars();
    assertTrue(lst.contains(x));
    assertTrue(lst.contains(y));
    assertTrue(lst.contains(z));
    assertTrue(lst.size() == 3);
  }

  @Test
  public void testVarsReuse() {
    // let's create: f(g(x), h(y,y))
    Variable x = new Var("x", baseType("o"), false);
    Variable y = new Var("x", baseType("o"), false);
    Term gx = unaryTerm("g", baseType("o"), x);
    Term hyy = TermFactory.createConstant("h", 2).apply(y).apply(y);
    Term term = TermFactory.createConstant("f", 2).apply(gx).apply(hyy);
    assertTrue(gx.vars() == x.vars());
    assertTrue(hyy.vars() == y.vars());
    assertTrue(term.vars().size() == 2);
  }

  @Test
  public void testSubtermGood() {
    Position p;
    Term s = twoArgFuncTerm();
    p = PositionFactory.empty;
    assertTrue(s.querySubterm(p).equals(s));
    p = PositionFactory.createArg(1, PositionFactory.empty);
    assertTrue(s.querySubterm(p).equals(constantTerm("c", baseType("a"))));
    p = PositionFactory.createArg(2, PositionFactory.createArg(1, PositionFactory.empty));
    assertTrue(s.querySubterm(p).equals(constantTerm("d", baseType("b"))));
  }

  @Test
  public void testHeadSubtermGood() {
    HeadPosition p;
    Term s = twoArgFuncTerm();
    p = new HeadPosition(PositionFactory.empty, 1);
    assertTrue(s.querySubterm(p).toString().equals("f(c)"));
    p = new HeadPosition(PositionFactory.createArg(1, PositionFactory.empty));
    assertTrue(s.querySubterm(p).equals(constantTerm("c", baseType("a"))));
    p = new HeadPosition(PositionFactory.createArg(2, PositionFactory.empty), 1);
    assertTrue(s.querySubterm(p).toString().equals("g"));
  }

  @Test(expected = IndexingError.class)
  public void testSubtermBad() {
    Term s = twoArgVarTerm();
    Position pos = PositionFactory.createArg(1,PositionFactory.createArg(2,PositionFactory.empty));
    Term t = s.querySubterm(pos);
  }

  @Test(expected = IndexingError.class)
  public void testHeadSubtermBad() {
    Term s = twoArgFuncTerm();
    HeadPosition pos = new HeadPosition(PositionFactory.createArg(2,PositionFactory.empty), 2);
    Term t = s.querySubterm(pos);
  }

  @Test
  public void testSubtermReplacementGood() {
    Variable z = new Var("Z", arrowType("Int", "Int"), false);
    Term s = new Application(z, constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(PositionFactory.createArg(1, PositionFactory.empty), s);
    assertTrue(s.toString().equals("Z(37)"));
    assertTrue(t.queryArgument(1).equals(s));
    assertTrue(t.toString().equals("Z(Z(37))"));
  }

  @Test
  public void testSubtermHeadReplacementGood() {
    Term s = twoArgFuncTerm();  // f(c, g(d))
    HeadPosition pos = new HeadPosition(PositionFactory.createArg(2, PositionFactory.empty), 1);
    Term a = constantTerm("a", baseType("A"));
    Var x = new Var("x", arrowType(baseType("A"), arrowType("b", "b")), true);
    Term t = s.replaceSubterm(pos, x.apply(a));
    assertTrue(t.toString().equals("f(c, x(a, d))"));
    Term q = t.replaceSubterm(pos, x.apply(a));
    assertTrue(t.equals(q));
    pos = new HeadPosition(PositionFactory.createArg(2, PositionFactory.empty));
    t = s.replaceSubterm(pos, constantTerm("B", baseType("b")));
    assertTrue(t.toString().equals("f(c, B)"));
  }

  @Test(expected = IndexingError.class)
  public void testSubtermReplacementBadPosition() {
    Var z = new Var("Z", arrowType("Int", "Int"), false);
    Term s = new Application(z, constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(PositionFactory.createArg(2, PositionFactory.empty), s);
  }

  @Test(expected = IndexingError.class)
  public void testSubtermHeadReplacementBadPosition() {
    Var z = new Var("Z", arrowType("Int", "Int"), false);
    Term s = new Application(z, constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(new HeadPosition(PositionFactory.createArg(2,
      PositionFactory.empty)), s);
  }

  @Test(expected = IndexingError.class)
  public void testSubtermHeadReplacementBadHeadPosition() {
    Constant f = new Constant("f", arrowType("Int", "Int"));
    Term s = new Application(f, constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(new HeadPosition(PositionFactory.empty, 2),
      constantTerm("a", baseType("B")));
  }

  @Test(expected = TypingError.class)
  public void testSubtermReplacementBadTypeSub() {
    Constant f = new Constant("f", arrowType("Int", "Bool"));
    Term s = new Application(f, constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(PositionFactory.createArg(1, PositionFactory.empty), s);
  }

  @Test(expected = TypingError.class)
  public void testSubtermReplacementBadTypeTop() {
    Variable z = new Var("Z", arrowType("Int", "Bool"), true);
    Term s = new Application(z, constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(PositionFactory.empty, constantTerm("42", baseType("Int")));
  }

  @Test(expected = TypingError.class)
  public void testSubtermHeadReplacementBadType() {
    Variable z = new Var("Z", arrowType("Int", "Bool"), true);
    Term s = new Application(z, constantTerm("37", baseType("Int")));
    Term replacement = constantTerm("f", arrowType("Int", "Int"));
    s.replaceSubterm(new HeadPosition(PositionFactory.empty, 1), replacement);
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
    FunctionSymbol f = new Constant("f", type);
    Term fc = new Application(f, c);
    fc.apply(c);
  }

  @Test
  public void testCorrectApplication() {
    Type o = baseType("o");
    Type a = baseType("a");
    Type type = arrowType(a, arrowType(o, a));
    Term c = constantTerm("c", arrowType(a, a));
    Term d = constantTerm("d", a);
    Variable x = new Var("x", type, false);
    Term xc = new Application(x, c.apply(d));
    Term xcb = xc.apply(constantTerm("b", o));
    assertTrue(xcb.toString().equals("x(c(d), b)"));
  }

  @Test
  public void testSubstituting() {
    Variable x = new Var("x", baseType("Int"), true);
    Variable y = new Var("y", baseType("Int"), false);
    Variable z = new Var("Z", arrowType(baseType("Int"), arrowType("Bool", "Int")), false);
    Term s = new Application(z, x, unaryTerm("f", baseType("Bool"), y));
      // Z(x, f(y))

    Term thirtyseven = constantTerm("37", baseType("Int"));
    FunctionSymbol g = new Constant("g", arrowType(baseType("o"),
                                         arrowType(baseType("Int"), arrowType("Bool", "Int"))));
    Term t = new Application(g, constantTerm("c", baseType("o")));

    Substitution gamma = new Subst(x, thirtyseven);
    gamma.extend(y, x);
    gamma.extend(z, t);

    Term q = s.substitute(gamma);
    assertTrue(q.toString().equals("g(c, 37, f(x))"));
  }

  @Test(expected = NullCallError.class)
  public void testNullMatch() {
    Term t = twoArgFuncTerm();
    Substitution subst = new Subst();
    t.match(null, subst);
  }

  @Test
  public void testFirstOrderMatching() {
    Type ii = baseType("Int");
    Variable x = new Var("x", ii, false);
    Variable y = new Var("y", ii, false);
    Variable z = new Var("z", ii, true);
    Type ty = arrowType(ii, arrowType(ii, ii));
    FunctionSymbol plus = new Constant("plus", ty);
    FunctionSymbol f = new Constant("f", ty);

    Term pattern1 = new Application(f, x, new Application(plus, y, z));
    Term pattern2 = new Application(f, x, new Application(plus, y, x));
    Term pattern3 = new Application(f, x, new Application(plus, y, y));
    Term pattern4 = new Application(plus, x, new Application(f, y, z));

    Term a = new Application(f, constantTerm("37", ii), z);
    Term combi = new Application(f, a, new Application(plus, y, a));

    Substitution subst1 = new Subst();
    Substitution subst2 = new Subst();
    Substitution subst3 = new Subst();
    Substitution subst4 = new Subst();

    assertTrue(pattern1.match(combi, subst1) == null);
    assertTrue(pattern2.match(combi, subst2) == null);
    assertTrue(pattern3.match(combi, subst3) != null);
    assertTrue(pattern4.match(combi, subst4) != null);

    assertTrue(subst1.domain().size() == 3);
    assertTrue(subst1.get(x).equals(a));
    assertTrue(subst1.get(y).equals(y));
    assertTrue(subst1.get(z).equals(a));

    assertTrue(subst2.domain().size() == 2);
    assertTrue(subst2.get(x).equals(a));
    assertTrue(subst2.get(y).equals(y));
  }

  @Test
  public void testBasicVarTermMatching() {
    Variable x = new Var("x", baseType("Int"), true);
    Variable z = new Var("Z", arrowType(baseType("Int"), arrowType("Int", "Int")), true);
    Term three = constantTerm("3", baseType("Int"));
    Term four = constantTerm("4", baseType("Int"));
    Type intintint = arrowType(baseType("Int"), arrowType("Int", "Int"));
    FunctionSymbol g = new Constant("g", intintint);
    FunctionSymbol h = new Constant("h", arrowType(baseType("Int"), intintint));
    Term pattern = new Application(z, three, x);
    Term fx = unaryTerm("f", baseType("Int"), x);
    List<Term> args = new ArrayList<Term>();
    args.add(fx);
    args.add(three);
    args.add(fx);
    Term s = new Application(h, args);
    Term t = new Application(g, four, three);

    // Z(3, x) is asked to match with h(f(x), 3, f(x))
    // This should map Z to h(f(x)) and x to f(x)
    Substitution gamma = pattern.match(s);
    Substitution delta = pattern.match(t);

    assertTrue(gamma != null);
    assertTrue(delta == null);

    assertTrue(gamma.get(x).equals(fx));
    assertTrue(gamma.get(z).equals(new Application(h, fx)));
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
    Term pattern = new Application(f, new Application(x, a), new Application(x, b));
      // f(x(a), x(b))

    Term s = new Application(f, new Application(g, a), new Application(g, b));
    Term t = new Application(f, new Application(h, a, a), new Application(h, a, b));
    Term q = new Application(f, new Application(h, a, a), new Application(h, b, b));
    Term u = new Application(f, a, b);

    Substitution gamma = pattern.match(s);
    assertTrue(gamma != null);
    assertTrue(gamma.get(x).equals(g));

    Substitution delta = pattern.match(t);
    assertTrue(delta != null);
    assertTrue(delta.get(x).equals(new Application(h, a)));

    assertTrue(pattern.match(q) == null);
    assertTrue(pattern.match(u) == null);
  }

  @Test
  public void testVarTermEquality() {
    Variable x = new Var("x", baseType("o"), false);
    Variable y = new Var("y", arrowType(baseType("o"), arrowType("o", "o")), false);
    List<Term> empty = new ArrayList<Term>();
    Term s1 = x;
    Term s2 = y;
    Term s3 = new Application(y, x);
    Term s4 = new Application(y, x, x);
    Term s5 = new Application(y, x, x);
    Term s6 = new Application(y, x, new Var("x", baseType("o"), false));
    
    assertTrue(s1.equals(s1));
    assertFalse(s1.equals(s2));
    assertFalse(s2.equals(s3));
    assertFalse(s3.equals(s4));
    assertFalse(s4.equals(s3));
    assertTrue(s4.equals(s5));
    assertFalse(s5.equals(s6));
  }

  @Test
  public void testFunctionalTermEquality() {
    Term s1 = constantTerm("x", baseType("o"));
    Term s2 = unaryTerm("x", baseType("o"), constantTerm("y", baseType("a")));
    Term s3 = unaryTerm("x", baseType("o"), constantTerm("y", baseType("a")));
    Term s4 = unaryTerm("x", baseType("a"), constantTerm("y", baseType("a")));
    assertFalse(s1.equals(s2));
    assertFalse(s2.equals(s1));
    assertTrue(s2.equals(s3));
    assertFalse(s2.equals(s4));
    assertFalse(s1.equals(new Var("x", baseType("o"), false)));
  }
}
