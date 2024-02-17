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

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;
import java.util.ArrayList;
import java.util.TreeMap;
import java.util.TreeSet;

import cora.exceptions.*;
import cora.utils.Pair;
import cora.types.Type;
import cora.terms.position.*;

public class ApplicationTest extends TermTestFoundation {
  @Test
  public void testUnaryWithNullArg() {
    Variable head = new Binder("x", arrowType("a", "b"));
    Term arg = null;
    assertThrows(NullInitialisationError.class, () ->new Application(head, arg));
  }

  @Test
  public void testBinaryWithNullHead() {
    assertThrows(NullInitialisationError.class, () ->
      new Application(null, constantTerm("a", baseType("b")),
                            constantTerm("a", baseType("c"))));
  }

  @Test
  public void testNullArgs() {
    Constant f = new Constant("f", arrowType("a", "b"));
    List<Term> args = null;
    assertThrows(NullInitialisationError.class, () -> new Application(f, args));
  }

  @Test
  public void testTooManyArgs() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Variable x = new Binder("x", type);
    List<Term> args = new ArrayList<Term>();
    args.add(constantTerm("c", baseType("a")));
    args.add(constantTerm("d", baseType("b")));
    args.add(constantTerm("e", baseType("a")));
    assertThrows(ArityError.class, () -> new Application(x, args));
  }

  @Test
  public void testTooManyArgsToApplication() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Variable x = new Binder("x", type);
    Term head = x.apply(constantTerm("c", baseType("a")));
    List<Term> args = new ArrayList<Term>();
    args.add(constantTerm("d", baseType("b")));
    args.add(constantTerm("e", baseType("a")));
    assertThrows(ArityError.class, () -> new Application(head, args));
  }

  @Test
  public void testConstructorBadArgType() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Term head = constantTerm("f", type);
    List<Term> args = new ArrayList<Term>();
    args.add(constantTerm("c", baseType("a")));
    args.add(constantTerm("d", baseType("a")));
    assertThrows(TypingError.class, () -> new Application(head, args));
  }

  @Test
  public void testConstructorBadArgTypeToApplication() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Term head = constantTerm("f", type).apply(constantTerm("c", baseType("a")));
    assertThrows(TypingError.class, () ->
      new Application(head, constantTerm("d", baseType("a"))));
  }

  @Test
  public void testCreateEmptyApplication() {
    Term head = new Var("x", arrowType(baseType("a"), arrowType("b", "a")));
    List<Term> args = new ArrayList<Term>();
    assertThrows(IllegalArgumentError.class, () -> new Application(head, args));
  }

  @Test
  public void testConstructApplicationFromApplicationHead() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Term head = constantTerm("f", type).apply(constantTerm("c", baseType("a")));
    Term t = new Application(head, constantTerm("d", baseType("b")));
    assertTrue(t.toString().equals("f(c, d)"));
    assertTrue(t.queryType().equals(baseType("a")));

    Term s = TermFactory.createApp(t, new ArrayList<Term>());
    assertTrue(s.equals(t));
  }

  @Test
  public void testFunctionalTermBasics() {
    Term t = twoArgFuncTerm();
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    assertTrue(t.isApplication());
    assertTrue(t.isApplicative());
    assertTrue(t.isFunctionalTerm());
    assertFalse(t.isConstant());
    assertFalse(t.isVariable());
    assertFalse(t.isVarTerm());
    assertTrue(t.isPattern());
    assertTrue(t.isApplication());
    assertTrue(t.queryRoot().equals(new Constant("f", type)));
    assertTrue(t.queryHead().equals(t.queryRoot()));
    assertTrue(t.queryHead().queryType().toString().equals("a → b → a"));
    assertTrue(t.queryType().equals(baseType("a")));
    assertTrue(t.isClosed());
    assertTrue(t.isGround());
    assertTrue(t.isTrueTerm());
    assertTrue(t.toString().equals("f(c, g(d))"));
    Term q = null;
    assertFalse(t.equals(q));
  }

  @Test
  public void testVarTermBasics() {
    Term t = twoArgVarTerm();
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    assertTrue(t.isApplication());
    assertTrue(t.isApplicative());
    assertTrue(t.isVarTerm());
    assertFalse(t.isConstant());
    assertFalse(t.isVariable());
    assertFalse(t.isFunctionalTerm());
    assertFalse(t.isPattern());
    assertTrue(t.isApplication());
    assertTrue(t.queryVariable().toString().equals("x"));
    assertTrue(t.queryHead().equals(t.queryVariable()));
    assertTrue(t.queryHead().queryType().toString().equals("a → b → a"));
    assertTrue(t.queryType().equals(baseType("a")));
    assertTrue(t.toString().equals("x(c, g(y))"));
    assertTrue(t.isClosed());
    assertFalse(t.isGround());
    assertTrue(t.isTrueTerm());
  }

  @Test
  public void testStoreFunctionSymbols() {
    Term t = twoArgFuncTerm();
    TreeSet<FunctionSymbol> set = new TreeSet<FunctionSymbol>();
    set.add(new Constant("c", baseType("a")));
    set.add(new Constant("f", baseType("b")));
    t.storeFunctionSymbols(set);
    assertTrue(set.size() == 5);
    assertTrue(set.toString().equals("[c, d, f, f, g]"));
  }

  @Test
  public void testTheory() {
    // +(x(0), y(z))
    Term zero = new IntegerValue(0);
    Type i = zero.queryType();
    Term x = new Var("x", arrowType(i, i));
    Term y = new Binder("y", i);
    Term t = new Application(new PlusSymbol(), x.apply(zero), y);
    assertTrue(t.isTheoryTerm());
    assertFalse(t.isValue());
    assertTrue(t.toValue() == null);
    // z(0) with z :: Int → a
    Var z = new Var("z", arrowType(i, baseType("a")));
    t = z.apply(zero);
    assertFalse(t.isTheoryTerm());
    // +(1, 2)
    t = new Application(new PlusSymbol(), new IntegerValue(1), new IntegerValue(2));
    assertTrue(t.isTheoryTerm());
    assertFalse(t.isValue());
    assertTrue(t.toValue() == null);
  }

  @Test
  public void testAbstractionTermBasics() {
    Variable x = new Binder("x", baseType("o"));
    Term abs = new Abstraction(x, x);
    Term t = new Application(abs, constantTerm("a", baseType("o")));
    assertTrue(t.isApplication());
    assertFalse(t.isApplicative());
    assertFalse(t.isVarTerm());
    assertFalse(t.isFunctionalTerm());
    assertFalse(t.isConstant());
    assertFalse(t.isVariable());
    assertFalse(t.isPattern());
    assertTrue(t.queryVariable() == x);
    assertTrue(t.queryHead() == abs);
    assertTrue(t.queryType().toString().equals("o"));
    assertTrue(t.toString().equals("(λx.x)(a)"));
  }

  @Test
  public void testPatternWithAbstractionBasics() {
    // x(y, λz.f(z))
    Variable x = new Binder("x", arrowType(baseType("A"), arrowType(
      arrowType("B", "A"), baseType("B"))));
    Variable y = new Var("y", baseType("A"));
    Variable z = new Binder("z", baseType("B"));
    Constant f = new Constant("f", arrowType("B", "A"));
    Term abs = new Abstraction(z, new Application(f, z));
    Term t = new Application(x, y, abs);

    assertTrue(t.isApplication());
    assertFalse(t.isApplicative());
    assertTrue(t.isPattern());
    assertTrue(t.isVarTerm());
    assertTrue(t.queryVariable() == x);
    assertTrue(t.queryHead() == x);
    assertTrue(t.queryType().equals(baseType("B")));
    assertTrue(t.toString().equals("x(y, λz.f(z))"));
  }

  @Test
  public void testIncorrectSubterm() {
    Term t = twoArgVarTerm();
    assertThrows(IndexingError.class, () -> t.queryArgument(0));
    assertThrows(IndexingError.class, () -> t.queryArgument(3));
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
  public void testMetaArguments() {
    // z⟨a,b⟩(c,d,e)
    Type o = baseType("o");
    Type type = arrowType(o, arrowType(o, arrowType(o, arrowType(o, arrowType(o, o)))));
    MetaVariable z = TermFactory.createMetaVar("Z", type, 2);
    Term zab = TermFactory.createMeta(z, constantTerm("a", o), constantTerm("b", o));
    Term term =
      zab.apply(constantTerm("c", o)).apply(constantTerm("d", o)).apply(constantTerm("e", o));
    assertTrue(term.numberArguments() == 3);
    assertTrue(term.numberMetaArguments() == 2);
    assertTrue(term.queryMetaArgument(1).equals(constantTerm("a", o)));
    assertTrue(term.queryMetaArgument(2).equals(constantTerm("b", o)));
    assertTrue(term.queryArgument(1).equals(constantTerm("c", o)));
  }

  @Test
  public void testImmediateHeadSubterms() {
    Term t = twoArgVarTerm();
    assertTrue(t.queryImmediateHeadSubterm(0).toString().equals("x"));
    assertTrue(t.queryImmediateHeadSubterm(1).toString().equals("x(c)"));
    assertTrue(t.queryImmediateHeadSubterm(2).toString().equals("x(c, g(y))"));
  }

  @Test
  public void testInappropriateRootRequest() {
    Term t = twoArgVarTerm();
    assertThrows(InappropriatePatternDataError.class, () -> t.queryRoot());
  }

  @Test
  public void testInappropriateVariableRequest() {
    Term t = twoArgFuncTerm();
    assertThrows(InappropriatePatternDataError.class, () -> t.queryVariable());
  }

  @Test
  public void testInappropriateAbstractionSubtermRequest() {
    Term t = twoArgFuncTerm();
    assertThrows(InappropriatePatternDataError.class, () -> t.queryAbstractionSubterm());
  }

  @Test
  public void testGoodAbstractionSubtermRequest() {
    Variable x = new Binder("x", baseType("o"));
    Term abs = new Abstraction(x, x);
    Term term = new Application(abs, constantTerm("a", baseType("o")));
    assertTrue(term.queryAbstractionSubterm() == x);
  }

  @Test
  public void testFirstOrderFunctionalTerm() {
    Type aa = arrowType("a", "a");
    Term s = twoArgFuncTerm();
    Term t = unaryTerm("h", aa, new Var("x", baseType("b")));
    Type utype = arrowType(baseType("a"), arrowType(aa, baseType("b")));
    Term q = new Application(new Constant("u", utype), s, t); 
    assertTrue(s.isFirstOrder());
    assertFalse(t.isFirstOrder());
    assertFalse(q.isFirstOrder());
  }

  @Test
  public void testFirstOrderVarTerm() {
    Variable y = new Binder("y", arrowType("o", "o"));
    Term x3 = new Application(y, constantTerm("c", baseType("o")));
    assertFalse(x3.isFirstOrder());
  }

  @Test
  public void testNonPatternDueToVariableApplication() {
    Variable x = new Var("x", arrowType("A", "B"));
    Term xa = new Application(x, constantTerm("a", baseType("A")));
    Term f = new Constant("f", arrowType("B", "B"));
    Term fxa = new Application(f, xa);
    assertFalse(fxa.isPattern());
    assertTrue(fxa.isSemiPattern());
  }

  @Test
  public void testBinderPattern() {
    Variable x = new Binder("x", arrowType(baseType("b"), arrowType("b", "a")));
    Variable y = new Var("y", baseType("b"));
    Variable z = new Var("z", arrowType("b", "b"));
    Term ba = new Constant("bb", arrowType("a", "b")).apply(constantTerm("aa", baseType("a")));
    List<Term> args = new ArrayList<Term>();
    args.add(y);
    args.add(ba);
    Term xybterm = new Application(x, args);  // x(y, bb(aa))
    assertTrue(xybterm.isPattern());    // we're allowed to apply binder variables
    assertTrue(xybterm.isSemiPattern());
    args.set(1, z.apply(ba));
    Term combiterm = new Application(x, args);  // x(y, bb(aa), z(bb(aa)))
    assertFalse(combiterm.isPattern()); // but the arguments do all need to be patterns :)
  }

  @Test
  public void testSemiNonPattern() {
    MetaVariable z = TermFactory.createMetaVar("Z", baseType("o"), arrowType("o", "o"));
    MetaVariable y = TermFactory.createMetaVar("Z", baseType("o"), arrowType("o", "o"));
    Term u = new Constant("u", baseType("o"));
    Term v = new Constant("v", arrowType(arrowType("o", "o"), baseType("o")));
    Variable x = new Binder("x", baseType("o"));
    Term zx = TermFactory.createMeta(z, x);
    Term zu = TermFactory.createMeta(z, u);
    // z[x](u)
    Term zxu = zx.apply(u);
    assertFalse(zxu.isPattern());
    assertTrue(zxu.isSemiPattern());
    // z[u](x)
    Term zux = zu.apply(x);
    assertFalse(zux.isPattern());
    assertFalse(zux.isSemiPattern());
    // v(z[x])
    Term vzx = v.apply(zx);
    assertTrue(vzx.isPattern());
    assertTrue(vzx.isSemiPattern());
    // v(z[u])
    Term vzu = v.apply(zu);
    assertFalse(vzu.isPattern());
    assertFalse(vzu.isSemiPattern());
  }

  @Test
  public void testSubterms() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Variable z = new Binder("Z", type);
    Term arg1 = unaryTerm("g", baseType("a"), new Var("x", baseType("b")));
    Term arg2 = constantTerm("c", baseType("b"));
    Term term = new Application(z, arg1, arg2);    // Z(g(x),c)
    List<Pair<Term,Position>> lst = term.querySubterms();
    assertTrue(lst.size() == 4);
    assertTrue(lst.get(0).snd().toString().equals("1.1.ε"));
    assertTrue(lst.get(0).fst().toString().equals("x"));
    assertTrue(lst.get(1).snd().toString().equals("1.ε"));
    assertTrue(lst.get(1).fst() == arg1);
    assertTrue(lst.get(2).snd().toString().equals("2.ε"));
    assertTrue(lst.get(2).fst() == term.queryArgument(2));
    assertTrue(lst.get(3).snd().toString().equals("ε"));
    assertTrue(lst.get(3).fst() == term);
  }

  @Test
  public void testFullPositionsForBetaRedex() {
    Variable x = new Binder("x", baseType("A"));
    Constant a = new Constant("a", baseType("A"));
    Constant b = new Constant("b", baseType("B"));
    Constant f = new Constant("f", arrowType(baseType("A"), arrowType("B", "C")));
    Term term = new Application(new Abstraction(x, f.apply(x)), a, b); // (λx.f(x))(a, b)
    List<Position> lst = term.queryPositions(false);
    assertTrue(lst.size() == 5);
    assertTrue(lst.get(0).toString().equals("0.1.ε"));
    assertTrue(lst.get(1).toString().equals("0.ε"));
    assertTrue(lst.get(2).toString().equals("1.ε"));
    assertTrue(lst.get(3).toString().equals("2.ε"));
    assertTrue(lst.get(4).toString().equals("ε"));
  }

  @Test
  public void testPartialPositions() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    Variable z = new Binder("Z", type);
    Term arg1 = unaryTerm("g", baseType("a"), new Var("x", baseType("b")));
    Term arg2 = constantTerm("c", baseType("b"));
    Term term = new Application(z, arg1, arg2);    // Z(g(x),c)
    List<Position> lst = term.queryPositions(true);
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
  public void testFreeReplaceables() {
    // let's create: Z(Z(x,h(λz.c(z))),g(J[y],x)), where Z, x and y are variables and J is a
    // meta-variable
    Variable z = new Binder("Z", arrowType(baseType("a"),arrowType("b","a")));
    FunctionSymbol g = new Constant("g", arrowType(baseType("b"),arrowType("a","b")));
    FunctionSymbol c = new Constant("c", arrowType("o", "o"));
    FunctionSymbol h = new Constant("h", arrowType(arrowType("o", "o"), baseType("b")));
    Variable x = new Binder("x", baseType("a"));
    Variable y = new Var("y", baseType("b"));
    Variable z2 = new Binder("z", baseType("o"));
    MetaVariable j = TermFactory.createMetaVar("J", arrowType("b", "b"), 1);
    Term jy = TermFactory.createMeta(j, y);
    Term hlambdazcz = new Application(h, new Abstraction(z2, c.apply(z2)));
    Term s = new Application(z, new Application(z, x, hlambdazcz), new Application(g, jy, x));
    ReplaceableList lst = s.freeReplaceables();
    assertTrue(lst.contains(x));
    assertTrue(lst.contains(y));
    assertTrue(lst.contains(z));
    assertTrue(lst.contains(j));
    assertTrue(lst.size() == 4);
  }

  @Test
  public void testFreeReplaceablesReuse() {
    // let's create: f(g(x), h(y,y))
    Variable x = new Var("x", baseType("o"));
    Variable y = new Var("x", baseType("o"));
    Term gx = unaryTerm("g", baseType("o"), x);
    Term hyy = TermFactory.createConstant("h", 2).apply(y).apply(y);
    Term term = TermFactory.createConstant("f", 2).apply(gx).apply(hyy);
    assertTrue(gx.freeReplaceables() == x.freeReplaceables());
    assertTrue(hyy.freeReplaceables() == y.freeReplaceables());
    assertTrue(term.freeReplaceables().size() == 2);
  }

  @Test
  public void testBoundVars() {
    // let's create: f(λx.Z(x), Y, g(λz.z, λx,u.h(x,y)))
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Variable z = new Binder("z", baseType("o"));
    Variable u = new Binder("u", baseType("o"));
    Variable bZ = new Var("Z", arrowType("o", "o"));
    Variable bY = new Var("Y", baseType("o"));
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

    ReplaceableList freeVars = fterm.freeReplaceables();
    ReplaceableList boundVars = fterm.boundVars();
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
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Variable bY = new Var("Y", baseType("o"));
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
  public void testMVars() {
    // let's create: a(f(Z[X], X), Y[b])
    Variable a = new Binder("a", arrowType(baseType("o"), arrowType("o", "o")));
    Variable b = new Binder("b", baseType("o"));
    Var x = new Var("Y", baseType("o"));
    MetaVariable y = TermFactory.createMetaVar("Y", arrowType("o", "o"), 1);
    MetaVariable z = TermFactory.createMetaVar("Z", arrowType("o", "o"), 1);
    Term zx = TermFactory.createMeta(z, x);
    Term f = constantTerm("f", arrowType(baseType("o"), arrowType("o", "o")));
    Term fzxx = TermFactory.createApp(f, zx, x);
    Term yb = TermFactory.createMeta(y, b);
    Term term = TermFactory.createApp(a, fzxx, yb);
    // let's see if all the mvars are as expected!
    Environment<MetaVariable> mvars = term.mvars();
    assertTrue(mvars.size() == 3);
    assertTrue(mvars.contains(x));
    assertTrue(mvars.contains(y));
    assertTrue(mvars.contains(z));
    mvars = fzxx.mvars();
    assertTrue(mvars.size() == 2);
    assertTrue(mvars.contains(x));
    assertFalse(mvars.contains(y));
    assertTrue(mvars.contains(z));
    mvars = yb.mvars();
    assertTrue(mvars.size() == 1);
  }

  @Test
  public void testFullSubtermGood() {
    Position p;
    Term s = twoArgFuncTerm();
    p = Position.empty;
    assertTrue(s.querySubterm(p).equals(s));
    p = new ArgumentPos(1, Position.empty);
    assertTrue(s.querySubterm(p).equals(constantTerm("c", baseType("a"))));
    p = new ArgumentPos(2, new ArgumentPos(1, Position.empty));
    assertTrue(s.querySubterm(p).equals(constantTerm("d", baseType("b"))));
  }

  @Test
  public void testPartialSubtermGood() {
    Term s = twoArgFuncTerm();
    Position p = new FinalPos(1);
    assertTrue(s.querySubterm(p).toString().equals("f(c)"));
    p = new ArgumentPos(2, new FinalPos(1));
    assertTrue(s.querySubterm(p).toString().equals("g"));
  }

  @Test
  public void testSubtermInHead() {
    // (λx.f(x))(a)
    Variable x = new Binder("x", baseType("o"));
    Term s = new Application(new Abstraction(x, unaryTerm("f", baseType("o"), x)),
                             constantTerm("a", baseType("o")));
    assertTrue(s.querySubterm(new LambdaPos(new ArgumentPos(1, Position.empty))) == x);
  }

  @Test
  public void testSubtermBad() {
    Term s = twoArgVarTerm();
    Position pos = new ArgumentPos(1, new ArgumentPos(2, Position.empty));
    assertThrows(IndexingError.class, () -> s.querySubterm(pos));
  }

  @Test
  public void testHeadSubtermBad() {
    Term s = twoArgFuncTerm();
    Position pos = new ArgumentPos(2, new FinalPos(2));
    assertThrows(IndexingError.class, () -> s.querySubterm(pos));
  }

  @Test
  public void testSubtermReplacementGood() {
    Variable z = new Var("Z", arrowType("Int", "Int"));
    Term s = new Application(z, constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(new ArgumentPos(1, Position.empty), s);
    assertTrue(s.toString().equals("Z(37)"));
    assertTrue(t.queryArgument(1).equals(s));
    assertTrue(t.toString().equals("Z(Z(37))"));
  }

  @Test
  public void testSubtermInHeadReplacementGood() {
    // (λxy.f(y,x))(a, b)
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Term f = constantTerm("f", arrowType(baseType("o"), arrowType("o", "o")));
    Term a = constantTerm("a", baseType("o"));
    Term b = constantTerm("b", baseType("o"));
    Term s = new Application(new Abstraction(x, new Abstraction(y, new Application(f, y, x))),
                             a, b);
    
    // replace y in f(y,x) by x
    Term t = s.replaceSubterm(Position.parse("0.0.1"), x);
    assertTrue(t.toString().equals("(λx.λy.f(x, x))(a, b)"));

    // replace f(y) by (λy.y)
    Term u = s.replaceSubterm(Position.parse("0.0.*1"), new Abstraction(y, y));
    assertTrue(u.toString().equals("(λx.λy.(λy1.y1)(x))(a, b)"));
  }

  @Test
  public void testSubtermHeadReplacementGood() {
    Term s = twoArgFuncTerm();  // f(c, g(d))
    Position pos = new ArgumentPos(2, new FinalPos(1));
    Term a = constantTerm("a", baseType("A"));
    Variable x = new Binder("x", arrowType(baseType("A"), arrowType("b", "b")));
    Term t = s.replaceSubterm(pos, x.apply(a));
    assertTrue(t.toString().equals("f(c, x(a, d))"));
    Term q = t.replaceSubterm(pos, x.apply(a));
    assertTrue(t.equals(q));
    pos = new ArgumentPos(2, Position.empty);
    t = s.replaceSubterm(pos, constantTerm("B", baseType("b")));
    assertTrue(t.toString().equals("f(c, B)"));
    assertTrue(s.toString().equals("f(c, g(d))"));
  }

  @Test
  public void testSubtermReplacementBadPosition() {
    Variable z = new Var("Z", arrowType("Int", "Int"));
    Term s = new Application(z, constantTerm("37", baseType("Int")));
    assertThrows(IndexingError.class, () ->
      s.replaceSubterm(new ArgumentPos(2, Position.empty), s));
  }

  @Test
  public void testSubtermHeadReplacementBadPosition() {
    Variable z = new Var("Z", arrowType("Int", "Int"));
    Term s = new Application(z, constantTerm("37", baseType("Int")));
    assertThrows(IndexingError.class, () ->
      s.replaceSubterm(new ArgumentPos(2, new FinalPos(1)), s));
  }

  @Test
  public void testSubtermHeadReplacementBadHeadPosition() {
    Constant f = new Constant("f", arrowType("Int", "Int"));
    Term s = new Application(f, constantTerm("37", baseType("Int")));
    assertThrows(IndexingError.class, () ->
      s.replaceSubterm(new FinalPos(2), constantTerm("a", baseType("B"))));
  }

  @Test
  public void testSubtermReplacementBadTypeSub() {
    Constant f = new Constant("f", arrowType("Int", "Bool"));
    Term s = new Application(f, constantTerm("37", baseType("Int")));
    assertThrows(TypingError.class, () ->
      s.replaceSubterm(new ArgumentPos(1, Position.empty), s));
  }

  @Test
  public void testSubtermReplacementBadTypeTop() {
    Variable z = new Binder("Z", arrowType("Int", "Bool"));
    Term s = new Application(z, constantTerm("37", baseType("Int")));
    assertThrows(TypingError.class, () ->
      s.replaceSubterm(Position.empty, constantTerm("42", baseType("Int"))));
  }

  @Test
  public void testSubtermHeadReplacementBadType() {
    Variable z = new Binder("Z", arrowType("Int", "Bool"));
    Term s = new Application(z, constantTerm("37", baseType("Int")));
    Term replacement = constantTerm("f", arrowType("Int", "Int"));
    assertThrows(TypingError.class, () ->
      s.replaceSubterm(new FinalPos(1), replacement));
  }

  @Test
  public void testApplyingBaseTerm() {
    Term s = twoArgVarTerm();
    Term t = constantTerm("37", baseType("Int"));
    assertThrows(ArityError.class, () -> s.apply(t));
  }

  @Test
  public void testApplyingBadType() {
    Type o = baseType("o");
    Type a = baseType("a");
    Type type = arrowType(a, arrowType(o, a));
    Term c = constantTerm("c", a);
    FunctionSymbol f = new Constant("f", type);
    Term fc = new Application(f, c);
    assertThrows(TypingError.class, () -> fc.apply(c));
  }

  @Test
  public void testCorrectApplication() {
    Type o = baseType("o");
    Type a = baseType("a");
    Type type = arrowType(a, arrowType(o, a));
    Term c = constantTerm("c", arrowType(a, a));
    Term d = constantTerm("d", a);
    Variable x = new Var("x", type);
    Term xc = new Application(x, c.apply(d));
    Term xcb = xc.apply(constantTerm("b", o));
    assertTrue(xcb.toString().equals("x(c(d), b)"));
  }

  @Test
  public void testApplicativeSubstituting() {
    Variable x = new Binder("x", baseType("Int"));
    Variable y = new Var("y", baseType("Int"));
    Variable z = new Var("Z", arrowType(baseType("Int"), arrowType("Bool", "Int")));
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
    Variable x = new Binder("X", arrowType(baseType("o"), arrowType(baseType("o"),
      arrowType("o", "o"))));
    Variable y = new Binder("y", baseType("o"));
    Variable z = new Binder("z", baseType("o"));
    Term term = new Application(new Application(x, a),
      new Application(f, new Abstraction(y, new Application(g, y, z))),
      new Application(f, new Abstraction(y, new Application(g, y, y))));
    // [X := λxy.h(y, z), y := a, z := g(a, y)]
    Term h = constantTerm("h", arrowType(baseType("o"), arrowType(baseType("o"),
      arrowType("o", "o"))));
    Variable x1 = new Binder("x", baseType("o"));
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
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("x", baseType("o"));
    Variable z = new Binder("x", baseType("o"));
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
    Variable x = new Binder("x", baseType("a"));
    Variable y = new Binder("y", arrowType("b", "b"));
    Variable z = new Binder("z", baseType("c"));
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

  @Test
  public void testNullMatch() {
    Term t = twoArgFuncTerm();
    Substitution subst = new Subst();
    assertThrows(NullCallError.class, () -> t.match(null, subst));
  }

  @Test
  public void testFirstOrderMatching() {
    Type ii = baseType("Int");
    Variable x = new Var("x", ii);
    Variable y = new Var("y", ii);
    Variable z = new Binder("z", ii);
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
    Variable x = new Binder("x", baseType("Int"));
    Variable z = new Binder("Z", arrowType(baseType("Int"), arrowType("Int", "Int")));
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
    Variable x = new Binder("x", arrowType("o", "o"));
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
    Variable x = new Var("x", baseType("o"));
    Variable y = new Var("y", arrowType(baseType("o"), arrowType("o", "o")));
    List<Term> empty = new ArrayList<Term>();
    Term s1 = x;
    Term s2 = y;
    Term s3 = new Application(y, x);
    Term s4 = new Application(y, x, x);
    Term s5 = new Application(y, x, x);
    Term s6 = new Application(y, x, new Var("x", baseType("o")));
    
    assertTrue(s1.equals(s1));
    assertFalse(s1.equals(s2));
    assertFalse(s2.equals(s3));
    assertFalse(s3.equals(s4));
    assertFalse(s4.equals(s3));
    assertTrue(s4.equals(s5));
    assertFalse(s5.equals(s6));
  }

  @Test
  public void testOnlySemiPattern() {
    // F⟨x⟩(a, Y) matched against both h(g(x), a, b) and h(g(x), b, a)
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Var("Y", baseType("o"));
    Term a = constantTerm("a", baseType("o"));
    Term b = constantTerm("b", baseType("o"));
    Term g = constantTerm("g", arrowType("o", "o"));
    Type oooo = arrowType(baseType("o"), arrowType(baseType("o"), arrowType("o", "o")));
    Term h = constantTerm("h", oooo);
    MetaVariable f = TermFactory.createMetaVar("F", oooo, 1); 
    Term term = new Application(TermFactory.createMeta(f, x), a, y); 

    Term m1 = new Application(h.apply(g.apply(x)), a, b); 
    Term m2 = new Application(h.apply(g.apply(x)), b, a); 

    Substitution subst = new Subst();
    subst.extend(x, x); 
    assertTrue(term.match(m1, subst) == null);
    assertTrue(subst.get(x) == x); 
    assertTrue(subst.get(y) == b); 
    assertTrue(subst.get(f).equals(new Abstraction(x, h.apply(g.apply(x)))));

    subst = new Subst();
    subst.extend(x, x); 
    assertTrue(term.match(m2, subst) != null);
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
    assertFalse(s1.equals(new Var("x", baseType("o"))));
  }

  @Test
  public void testAlphaEquality() {
    // (λx.x) (f(y, λx.x)) =[y:=1,z:=1] (λy.y) (f(z, λx.x))
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Variable z = new Binder("z", baseType("o"));
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
    Variable a = new Binder("x", arrowType(baseType("o"), arrowType("o", "o")));
    Variable b = new Var("x", baseType("o"));
    Variable c = new Var("x", baseType("o"));
    Term combi = new Application(a, b, c);
    assertTrue(combi.toString().equals("x__3(x__1, x__2)"));
    StringBuilder builder = new StringBuilder();
    combi.addToString(builder, null);
    assertTrue(builder.toString().equals("x(x, x)"));
    TreeMap<Replaceable,String> naming = new TreeMap<Replaceable,String>();
    naming.put(b, "y");
    builder.setLength(0);
    combi.addToString(builder, naming);
    assertTrue(builder.toString().equals("x(y, x)"));
  }

  @Test
  public void testCorrectPrintingWithoundVariables() {
    // (λx0.x0)(f(g(x1, x2), λx3.g(x2, x3), λx4.λx3.g(x3,x4)))
    Variable x0 = new Binder("x", baseType("o"));
    Variable x1 = new Binder("x", baseType("o"));
    Variable x2 = new Binder("x", baseType("o"));
    Variable x3 = new Binder("x", baseType("o"));
    Variable x4 = new Binder("x", baseType("o"));
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
