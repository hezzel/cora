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
import java.util.TreeMap;
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
    Term q = null;
    assertFalse(t.equals(q));
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

  @Test(expected = InappropriatePatternDataError.class)
  public void testInappropriateAbstractionSubtermRequest() {
    Variable x = new Var("x", baseType("o"), true);
    Term abs = new Abstraction(x, x);
    Term term = new Application(abs, constantTerm("a", baseType("o")));
    term.queryAbstractionSubterm();
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
  public void testNonPatternDueToVariableApplication() {
    Var x = new Var("x", arrowType("A", "B"), false);
    Term xa = new Application(x, constantTerm("a", baseType("A")));
    Term f = new Constant("f", arrowType("B", "B"));
    Term fxa = new Application(f, xa);
    assertFalse(fxa.isPattern());
  }

  @Test
  public void testNonPatternDueToAbstractionAppplication() {
    // (λx.x)(a)
    Var x = new Var("x", baseType("A"), true);
    Term term = new Application(new Abstraction(x, x), constantTerm("a", baseType("A")));
    assertFalse(term.isPattern());
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
  public void testPositionsForBetaRedex() {
    Variable x = new Var("x", baseType("A"), true);
    Constant a = new Constant("a", baseType("A"));
    Constant b = new Constant("b", baseType("B"));
    Constant f = new Constant("f", arrowType(baseType("A"), arrowType("B", "C")));
    Term term = new Application(new Abstraction(x, f.apply(x)), a, b); // (λx.f(x))(a, b)
    List<Path> lst = term.queryPositions();
    assertTrue(lst.size() == 5);
    assertTrue(lst.get(0).toString().equals("0.1.ε"));
    assertTrue(lst.get(0).queryCorrespondingSubterm() == x);
    assertTrue(lst.get(1).toString().equals("0.ε"));
    assertTrue(lst.get(2).toString().equals("1.ε"));
    assertTrue(lst.get(3).toString().equals("2.ε"));
    assertTrue(lst.get(4).toString().equals("ε"));
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
  public void testFreeVars() {
    // let's create: Z(Z(x,h(λz.c(z))),g(y,x)), where Z, x and y are variables
    Variable z = new Var("Z", arrowType(baseType("a"),arrowType("b","a")), true);
    FunctionSymbol g = new Constant("g", arrowType(baseType("b"),arrowType("a","b")));
    FunctionSymbol c = new Constant("c", arrowType("o", "o"));
    FunctionSymbol h = new Constant("h", arrowType(arrowType("o", "o"), baseType("b")));
    Variable x = new Var("x", baseType("a"), true);
    Variable y = new Var("y", baseType("b"), false);
    Variable z2 = new Var("z", baseType("o"), true);
    Term hlambdazcz = new Application(h, new Abstraction(z2, c.apply(z2)));
    Term s = new Application(z, new Application(z, x, hlambdazcz), new Application(g, y, x));
    VariableList lst = s.vars();
    assertTrue(lst.contains(x));
    assertTrue(lst.contains(y));
    assertTrue(lst.contains(z));
    assertTrue(lst.size() == 3);
  }

  @Test
  public void testFreeVarsReuse() {
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
  public void testBoundVars() {
    // let's create: f(λx.Z(x), Y, g(λz.z, λx,u.h(x,y)))
    Variable x = new Var("x", baseType("o"), true);
    Variable y = new Var("y", baseType("o"), true);
    Variable z = new Var("z", baseType("o"), true);
    Variable u = new Var("u", baseType("o"), true);
    Variable bZ = new Var("Z", arrowType("o", "o"), false);
    Variable bY = new Var("Y", baseType("o"), false);
    FunctionSymbol h = new Constant("h", arrowType(baseType("o"), arrowType("o", "o")));
    FunctionSymbol g = new Constant("g", arrowType(arrowType("o", "o"),
      arrowType(arrowType(baseType("o"), arrowType("o", "o")), baseType("o"))));
    FunctionSymbol f = new Constant("f",
      arrowType(arrowType("o", "o"), arrowType(baseType("o"), arrowType("o", "o"))));
    Term ahxy = new Abstraction(x, new Abstraction(u, new Application(h, x, y)));
    Term az = new Abstraction(z, z);
    Term gterm = new Application(g, az, ahxy);
    Term aZx = new Abstraction(x, new Application(bZ, x));
    Term fterm = new Application(f, aZx, bY).apply(gterm);

    VariableList freeVars = fterm.vars();
    VariableList boundVars = fterm.boundVars();
    assertTrue(freeVars.size() == 3);
    assertTrue(boundVars.size() == 3);
    assertTrue(boundVars.contains(x));
    assertTrue(boundVars.contains(z));
    assertTrue(boundVars.contains(u));
    assertTrue(freeVars.contains(y));
    assertTrue(freeVars.contains(bY));
    assertTrue(freeVars.contains(bZ));
  }

  @Test
  public void testBoundVarsReuse() {
    Variable x = new Var("x", baseType("o"), true);
    Variable y = new Var("y", baseType("o"), true);
    Variable bY = new Var("Y", baseType("o"), false);
    Type oo = arrowType("o", "o");
    Constant f = new Constant("f", arrowType(baseType("o"), oo));
    Constant g = new Constant("g", arrowType(oo, baseType("o")));
    Constant h = new Constant("h", arrowType(baseType("o"), arrowType(oo, oo)));
    Constant i = new Constant("i", arrowType(oo, arrowType(oo, oo)));
    Constant b = new Constant("B", baseType("o"));
    // let's create: (λxy.f(x,y))(g(λx.x), g(λy.y))
    Term ax = new Abstraction(x, x);
    Term gx = g.apply(ax);
    Term gy = g.apply(new Abstraction(y, y));
    Term head = new Abstraction(x, new Abstraction(y, new Application(f, x, y)));
    Term term1 = new Application(head, gx, gy);
    assertTrue(ax.boundVars() == gx.boundVars());
    assertTrue(term1.boundVars() == head.boundVars());
    // let's create: h(Y, λx.x, B)
    Term term2 = (new Application(h, bY, ax)).apply(b);
    assertTrue(term2.boundVars() == ax.boundVars());
    // let's create: i(λx.x, λy.f(g(λx.x), y))
    Term fterm = new Application(f, gx, y);
    Term afterm = new Abstraction(y, fterm);
    Term term3 = new Application(i, ax, afterm);
    assertTrue(term3.boundVars() == afterm.boundVars());
    assertFalse(afterm.boundVars() == fterm.boundVars());
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

  @Test
  public void testSubtermInHead() {
    // (λx.f(x))(a)
    Var x = new Var("x", baseType("o"), true);
    Term s = new Application(new Abstraction(x, unaryTerm("f", baseType("o"), x)),
                             constantTerm("a", baseType("o")));
    assertTrue(s.querySubterm(PositionFactory.createLambda(PositionFactory.createArg(1,
      PositionFactory.empty))) == x);
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
  public void testSubtermInHeadReplacementGood() {
    // (λxy.f(y,x))(a, b)
    Variable x = new Var("x", baseType("o"), true);
    Variable y = new Var("y", baseType("o"), true);
    Term f = constantTerm("f", arrowType(baseType("o"), arrowType("o", "o")));
    Term a = constantTerm("a", baseType("o"));
    Term b = constantTerm("b", baseType("o"));
    Term s = new Application(new Abstraction(x, new Abstraction(y, new Application(f, y, x))),
                             a, b);
    
    // replace y in f(y,x) by x
    Term t = s.replaceSubterm(PositionFactory.parsePos("0.0.1"), x);
    assertTrue(t.toString().equals("(λx.λy.f(x, x))(a, b)"));

    // replace f(y) by (λy.y)
    Term u = s.replaceSubterm(PositionFactory.parseHPos("0.0.*1"), new Abstraction(y, y));
    assertTrue(u.toString().equals("(λx.λy.(λy1.y1)(x))(a, b)"));
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
    assertTrue(s.toString().equals("f(c, g(d))"));
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
  public void testApplicativeSubstituting() {
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

  @Test
  public void testLambdaSubstituting() {
    // X(a, f(λy.g(y, z)), f(λy.g(y, y)))
    Term g = constantTerm("g", arrowType(baseType("o"), arrowType("o", "o")));
    Term f = constantTerm("f", arrowType(arrowType("o", "o"), baseType("o")));
    Term a = constantTerm("a", baseType("o"));
    Var x = new Var("X", arrowType(baseType("o"), arrowType(baseType("o"),
      arrowType("o", "o"))), true);
    Var y = new Var("y", baseType("o"), true);
    Var z = new Var("z", baseType("o"), true);
    Term term = new Application(new Application(x, a),
      new Application(f, new Abstraction(y, new Application(g, y, z))),
      new Application(f, new Abstraction(y, new Application(g, y, y))));
    // [X := λxy.h(y, z), y := a, z := g(a, y)]
    Term h = constantTerm("h", arrowType(baseType("o"), arrowType(baseType("o"),
      arrowType("o", "o"))));
    Var x1 = new Var("x", baseType("o"), true);
    Subst subst = new Subst();
    subst.extend(x, new Abstraction(x1, new Abstraction(y, new Application(h, y, z))));
    subst.extend(y, a);
    subst.extend(z, new Application(g, a, y));

    Term s = term.substitute(subst);
    assertTrue(s.toString().equals("(λx.λy1.h(y1, z))(a, f(λy1.g(y1, g(a, y))), f(λy1.g(y1, y1)))"));
  }

  @Test
  public void testRefreshBinders() {
    // (λxy.f(x,y))(g(λz.z), g(λz.z))
    Variable x = new Var("x", baseType("o"), true);
    Variable y = new Var("x", baseType("o"), true);
    Variable z = new Var("x", baseType("o"), true);
    Term f = constantTerm("f", arrowType(baseType("o"), arrowType("o", "o")));
    Term g = constantTerm("g", arrowType(arrowType("o", "o"), baseType("o")));
    Term zz = new Abstraction(z, z);
    Term abs = new Abstraction(x, new Abstraction(y, new Application(f, x, y)));
    Term term = new Application(abs, new Application(g, zz), new Application(g, zz));

    Term t = term.refreshBinders();
    assertTrue(t.equals(term));
    Variable a = t.queryVariable();
    Variable b = t.queryHead().queryAbstractionSubterm().queryVariable();
    Variable c = t.queryArgument(1).queryArgument(1).queryVariable();
    Variable d = t.queryArgument(2).queryArgument(1).queryVariable();

    assertTrue(a.compareTo(z) > 0);
    assertTrue(b.compareTo(z) > 0);
    assertTrue(c.compareTo(z) > 0);
    assertTrue(d.compareTo(z) > 0);
    assertFalse(a.equals(b));
    assertFalse(a.equals(c));
    assertFalse(a.equals(d));
    assertFalse(b.equals(c));
    assertFalse(b.equals(d));
    assertFalse(c.equals(d));
  }

  @Test
  public void testWellbehaved() {
    // f(x, λy.g(y, x), λx.x, λz.z, y)
    Var x = new Var("x", baseType("a"), true);
    Var y = new Var("y", arrowType("b", "b"), true);
    Var z = new Var("z", baseType("c"), true);
    Term g = new Constant("g", arrowType(arrowType("b", "b"), arrowType("a", "d")));
    Term f = new Constant("f", arrowType(
      baseType("a"), arrowType(
      arrowType(arrowType("b", "b"), baseType("d")), arrowType(
      arrowType("a", "a"), arrowType(
      arrowType("c", "c"), arrowType(
      arrowType("b", "b"), baseType("e")))))));
    Term arg2 = new Abstraction(y, new Application(g, y, x));
    Term arg3 = new Abstraction(x, x);
    Term arg4 = new Abstraction(z, z);
    Term s = new Application(new Application(new Application(f, x, arg2), arg3, arg4), y);
    assertTrue(s.queryArgument(1) == x);
    assertTrue(s.queryArgument(2).queryVariable() != y);
    assertTrue(s.queryArgument(2).queryAbstractionSubterm().queryArgument(1) ==
               s.queryArgument(2).queryVariable());
    assertTrue(s.queryArgument(2).queryAbstractionSubterm().queryArgument(2) == x);
    assertTrue(s.queryArgument(3).queryVariable() != x);
    assertTrue(s.queryArgument(3).queryAbstractionSubterm().queryVariable() ==
               s.queryArgument(3).queryVariable());
    assertTrue(s.queryArgument(4).queryVariable() == z);
    assertTrue(s.queryArgument(5).queryVariable() == y);
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

  @Test
  public void testAlphaEquality() {
    // (λx.x) (f(y, λx.x)) =[y:=1,z:=1] (λy.y) (f(z, λx.x))
    Var x = new Var("x", baseType("o"), true);
    Var y = new Var("y", baseType("o"), true);
    Var z = new Var("z", baseType("o"), true);
    Constant f = new Constant("f", arrowType(baseType("o"), arrowType(
      arrowType("o", "o"), baseType("o"))));
    TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
    TreeMap<Variable,Integer> xi = new TreeMap<Variable,Integer>();
    mu.put(y, 1);
    xi.put(z, 1);
    Term xx = new Abstraction(x, x);
    Term s = new Application(xx, new Application(f, y, xx));
    Term t = new Application(new Abstraction(y, y), new Application(f, z, xx));
    assertTrue(s.equals(s));
    assertFalse(s.equals(t));
    assertTrue(s.alphaEquals(t, mu, xi, 2));
  }

  @Test
  public void testFreeVariableRenaming() {
    Variable a = new Var("x", arrowType(baseType("o"), arrowType("o", "o")), true);
    Variable b = new Var("x", baseType("o"), false);
    Variable c = new Var("x", baseType("o"), false);
    Term combi = new Application(a, b, c);
    assertTrue(combi.toString().equals("x__1(x__2, x__3)"));
    StringBuilder builder = new StringBuilder();
    combi.addToString(builder, null);
    assertTrue(builder.toString().equals("x(x, x)"));
    TreeMap<Variable,String> naming = new TreeMap<Variable,String>();
    naming.put(b, "y");
    builder.setLength(0);
    combi.addToString(builder, naming);
    assertTrue(builder.toString().equals("x(y, x)"));
  }

  @Test
  public void testCorrectPrintingWithoundVariables() {
    // (λx0.x0)(f(g(x1, x2), λx3.g(x2, x3), λx4.λx3.g(x3,x4)))
    Variable x0 = new Var("x", baseType("o"), true);
    Variable x1 = new Var("x", baseType("o"), true);
    Variable x2 = new Var("x", baseType("o"), true);
    Variable x3 = new Var("x", baseType("o"), true);
    Variable x4 = new Var("x", baseType("o"), true);
    Term g = constantTerm("g", arrowType(baseType("o"), arrowType("o", "o")));
    Term f = constantTerm("f", arrowType(baseType("o"), arrowType(
      arrowType("o", "o"), arrowType(arrowType(baseType("o"), arrowType("o", "o")),
      baseType("o")))));
    Term abs = new Abstraction(x0,x0);
    Term arg1 = new Application(g, x1, x2);
    Term arg2 = new Abstraction(x3, new Application(g, x2, x3));
    Term arg3 = new Abstraction(x4, new Abstraction(x3, new Application(g, x3, x4)));
    Term total = new Application(abs, (new Application(f, arg1, arg2)).apply(arg3));
    assertTrue(total.toString().equals(
      "(λx1.x1)(f(g(x__1, x__2), λx1.g(x__2, x1), λx1.λx2.g(x2, x1)))"));
  }
}
