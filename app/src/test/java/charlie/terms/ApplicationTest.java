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
import java.util.List;
import java.util.ArrayList;
import java.util.TreeMap;
import java.util.TreeSet;

import charlie.util.Pair;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.types.TVarSet;
import charlie.parser.CoraParser;
import charlie.terms.position.*;
import charlie.terms.replaceable.ReplaceableSet;

public class ApplicationTest {
  private Type type(String desc) { return CoraParser.readType(desc); }

  protected Term unaryTerm(String name, Type output, Term arg) {
    Type arrtype = TypeFactory.createArrow(arg.queryType(), output);
    FunctionSymbol f = new Constant(name, arrtype);
    return new Application(f, arg);
  }

  protected Term twoArgVarTerm() {
    Variable x = TermFactory.createVar("x", type("a -> b -> a"));
    Term arg1 = new Constant("c", type("a"));
    Term arg2 = unaryTerm("g", type("b"), TermFactory.createVar("y", type("b")));
    return new Application(x, arg1, arg2);
  }

  protected Term twoArgFuncTerm() {
    FunctionSymbol f = new Constant("f", type("a -> b -> a"));
    Term arg1 = new Constant("c", type("a"));
    Term arg2 = unaryTerm("g", type("b"), new Constant("d", type("b")));
    return new Application(f, arg1, arg2);
  }

  @Test
  public void testUnaryWithNullArg() {
    Variable head = new Binder("x", type("a -> b"));
    Term arg = null;
    assertThrows(NullPointerException.class, () ->new Application(head, arg));
  }

  @Test
  public void testBinaryWithNullHead() {
    assertThrows(NullPointerException.class, () ->
      new Application(null, new Constant("a", type("b")),
                            new Constant("a", type("c"))));
  }

  @Test
  public void testNullArgs() {
    Constant f = new Constant("f", type("a -> b"));
    List<Term> args = null;
    assertThrows(NullPointerException.class, () -> new Application(f, args));
  }

  @Test
  public void testTooManyArgs() {
    Type type = type("a -> b -> a");
    Variable x = new Binder("x", type);
    List<Term> args = new ArrayList<Term>();
    args.add(new Constant("c", type("a")));
    args.add(new Constant("d", type("b")));
    args.add(new Constant("e", type("a")));
    assertThrows(TypingException.class, () -> new Application(x, args));
  }

  @Test
  public void testTooManyArgsToApplication() {
    Type type = type("a -> b -> a");
    Variable x = new Binder("x", type);
    Term head = x.apply(new Constant("c", type("a")));
    List<Term> args = new ArrayList<Term>();
    args.add(new Constant("d", type("b")));
    args.add(new Constant("e", type("a")));
    assertThrows(TypingException.class, () -> new Application(head, args));
  }

  @Test
  public void testConstructorBadArgTypeToListApplication() {
    Type type = type("a -> b -> a");
    Term head = new Constant("f", type);
    List<Term> args = new ArrayList<Term>();
    args.add(new Constant("c", type("a")));
    args.add(new Constant("d", type("a")));
    assertThrows(TypingException.class, () -> new Application(head, args));
  }

  @Test
  public void testConstructorBadArgTypeToSingleApplication() {
    Type type = type("a -> b -> a");
    Term head = new Constant("f", type).apply(new Constant("c", type("a")));
    assertThrows(TypingException.class, () ->
      new Application(head, new Constant("d", type("a"))));
  }

  @Test
  public void testCreateEmptyApplication() {
    Term head = new Var("x", type("a -> b -> a"));
    List<Term> args = new ArrayList<Term>();
    assertThrows(IllegalArgumentException.class, () -> new Application(head, args));
  }

  @Test
  public void testConstructApplicationFromApplicationHead() {
    Type type = type("a -> b -> a");
    Term head = new Constant("f", type).apply(new Constant("c", type("a")));
    Term t = new Application(head, new Constant("d", type("b")));
    assertTrue(t.toString().equals("f(c, d)"));
    assertTrue(t.queryType().equals(type("a")));

    Term s = TermFactory.createApp(t, new ArrayList<Term>());
    assertTrue(s.equals(t));
  }

  @Test
  public void testFunctionalTermBasics() {
    Term t = twoArgFuncTerm();
    assertTrue(t.isApplication());
    assertTrue(t.isApplicative());
    assertTrue(t.isFunctionalTerm());
    assertFalse(t.isConstant());
    assertFalse(t.isVariable());
    assertFalse(t.isVarTerm());
    assertTrue(t.isPattern());
    assertTrue(t.isApplication());
    assertTrue(t.queryRoot().equals(new Constant("f", type("a -> b-> a"))));
    assertTrue(t.queryHead().equals(t.queryRoot()));
    assertTrue(t.queryHead().queryType().toString().equals("a → b → a"));
    assertTrue(t.queryType().equals(type("a")));
    assertTrue(t.isClosed());
    assertTrue(t.isGround());
    assertTrue(t.isTrueTerm());
    assertTrue(t.toString().equals("f(c, g(d))"));
    Term q = null;
    assertFalse(t.equals(q));
    assertTrue(t.isMonomorphic());
  }

  @Test
  public void testVarTermBasics() {
    Term t = twoArgVarTerm();
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
    assertTrue(t.queryType().equals(type("a")));
    assertTrue(t.toString().equals("x(c, g(y))"));
    assertTrue(t.isClosed());
    assertFalse(t.isGround());
    assertTrue(t.isTrueTerm());
    assertTrue(t.isLinear());
    assertTrue(t.isMonomorphic());
  }

  @Test
  public void testLinearity() {
    Term f = new Constant("f", type("o -> o -> o"));
    Term g = new Constant("g", type("(o -> o) -> (o -> o) -> o"));
    Term h = new Constant("h", type("o -> o -> o -> o"));
    Variable x = TermFactory.createVar("x", type("o"));
    Variable y = TermFactory.createBinder("y", type("o"));
    Variable z = TermFactory.createBinder("z", type("o"));
    MetaVariable zz = TermFactory.createMetaVar("Z", type("o -> o"), 1);
    MetaVariable hh = TermFactory.createMetaVar("h", type("o -> o"), 1);
    Term zy = TermFactory.createMeta(zz, y);
    Term hy = TermFactory.createMeta(hh, y);
    Term hz = TermFactory.createMeta(hh, z);
    // f(x, x)
    Term fxx = new Application(f, x, x);
    assertFalse(fxx.isLinear());
    // g(λz.H[z], λy.H[y])
    Term ghh = new Application(g, new Abstraction(z, hz), new Abstraction(y, hy));
    assertFalse(ghh.isLinear());
    // λy.h(Z[y], y, H[y])
    Term hzh = new Abstraction(y, (new Application(h, zy, y)).apply(hy));
    assertTrue(hzh.isLinear());
  }

  @Test
  public void testStoreFunctionSymbols() {
    Term t = twoArgFuncTerm();
    TreeSet<FunctionSymbol> set = new TreeSet<FunctionSymbol>();
    set.add(new Constant("c", type("a")));
    set.add(new Constant("f", type("b")));
    t.storeFunctionSymbols(set);
    assertTrue(set.size() == 5);
    assertTrue(set.toString().equals("[c, d, f, f, g]"));
  }

  @Test
  public void testAbstractionTermBasics() {
    Variable x = new Binder("x", type("o"));
    Term abs = new Abstraction(x, x);
    Term t = new Application(abs, new Constant("a", type("o")));
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
    Variable x = new Binder("x", type("A -> (B -> A) -> B"));
    Variable y = new Var("y", type("A"));
    Variable z = new Binder("z", type("B"));
    Constant f = new Constant("f", type("B -> A"));
    Term abs = new Abstraction(z, new Application(f, z));
    Term t = new Application(x, y, abs);

    assertTrue(t.isApplication());
    assertFalse(t.isApplicative());
    assertTrue(t.isPattern());
    assertTrue(t.isVarTerm());
    assertTrue(t.queryVariable() == x);
    assertTrue(t.queryHead() == x);
    assertTrue(t.queryType().equals(type("B")));
    assertTrue(t.toString().equals("x(y, λz.f(z))"));
  }

  @Test
  public void testIncorrectSubterm() {
    Term t = twoArgVarTerm();
    assertThrows(IndexOutOfBoundsException.class, () -> t.queryArgument(0));
    assertThrows(IndexOutOfBoundsException.class, () -> t.queryArgument(3));
  }

  @Test
  public void testArguments() {
    Term t = twoArgFuncTerm();
    assertTrue(t.queryNumberArguments() == 2);
    assertTrue(t.queryArgument(1).equals(new Constant("c", type("a"))));
    assertTrue(t.queryArgument(2).toString().equals("g(d)"));
    List<Term> args = t.listArguments();
    assertTrue(args.get(0) == t.queryArgument(1));
    assertTrue(args.get(1) == t.queryArgument(2));
    assertTrue(args.size() == 2);
  }

  @Test
  public void testMetaArguments() {
    // z⟨a,b⟩(c,d,e)
    Type o = type("o");
    Type type = type("o -> o -> o -> o -> o -> o");
    MetaVariable z = TermFactory.createMetaVar("Z", type, 2);
    Term zab = TermFactory.createMeta(z, new Constant("a", o), new Constant("b", o));
    Term term =
      zab.apply(new Constant("c", o)).apply(new Constant("d", o)).apply(new Constant("e", o));
    assertTrue(term.queryNumberArguments() == 3);
    assertTrue(term.queryNumberMetaArguments() == 2);
    assertTrue(term.queryMetaArgument(1).equals(new Constant("a", o)));
    assertTrue(term.queryMetaArgument(2).equals(new Constant("b", o)));
    assertTrue(term.queryArgument(1).equals(new Constant("c", o)));
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
    assertThrows(InappropriatePatternDataException.class, () -> t.queryRoot());
  }

  @Test
  public void testInappropriateVariableRequest() {
    Term t = twoArgFuncTerm();
    assertThrows(InappropriatePatternDataException.class, () -> t.queryVariable());
  }

  @Test
  public void testInappropriateAbstractionSubtermRequest() {
    Term t = twoArgFuncTerm();
    assertThrows(InappropriatePatternDataException.class, () -> t.queryAbstractionSubterm());
  }

  @Test
  public void testGoodAbstractionSubtermRequest() {
    Variable x = new Binder("x", type("o"));
    Term abs = new Abstraction(x, x);
    Term term = new Application(abs, new Constant("a", type("o")));
    assertTrue(term.queryAbstractionSubterm() == x);
  }

  @Test
  public void testFirstOrderFunctionalTerm() {
    Type aa = type("a -> a");
    Term s = twoArgFuncTerm();
    Term t = unaryTerm("h", aa, new Var("x", type("b")));
    Type utype = type("a -> (a -> a) -> b");
    Term q = new Application(new Constant("u", utype), s, t); 
    assertTrue(s.isFirstOrder());
    assertFalse(t.isFirstOrder());
    assertFalse(q.isFirstOrder());
  }

  @Test
  public void testFirstOrderVarTerm() {
    Variable y = new Binder("y", type("o -> o"));
    Term x3 = new Application(y, new Constant("c", type("o")));
    assertFalse(x3.isFirstOrder());
  }

  @Test
  public void testNonPatternDueToVariableApplication() {
    Variable x = new Var("x", type("A -> B"));
    Term xa = new Application(x, new Constant("a", type("A")));
    Term f = new Constant("f", type("B -> B"));
    Term fxa = new Application(f, xa);
    assertFalse(fxa.isPattern());
    assertTrue(fxa.isSemiPattern());
  }

  @Test
  public void testBinderPattern() {
    Variable x = new Binder("x", type("b -> b -> a"));
    Variable y = new Var("y", type("b"));
    Variable z = new Var("z", type("b -> b"));
    Term ba = new Constant("bb", type("a -> b")).apply(new Constant("aa", type("a")));
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
    MetaVariable z = TermFactory.createMetaVar("Z", type("o"), type("o -> o"));
    Term u = new Constant("u", type("o"));
    Term v = new Constant("v", type("(o -> o) -> o"));
    Variable x = new Binder("x", type("o"));
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
    Type type = type("a -> b ->a");
    Variable z = new Binder("Z", type);
    Term arg1 = unaryTerm("g", type("a"), new Var("x", type("b")));
    Term arg2 = new Constant("c", type("b"));
    Term term = new Application(z, arg1, arg2);    // Z(g(x),c)
    List<Pair<Term,Position>> lst = term.listSubterms();
    assertTrue(lst.size() == 4);
    assertTrue(lst.get(0).snd().toString().equals("1.1"));
    assertTrue(lst.get(0).fst().toString().equals("x"));
    assertTrue(lst.get(1).snd().toString().equals("1"));
    assertTrue(lst.get(1).fst() == arg1);
    assertTrue(lst.get(2).snd().toString().equals("2"));
    assertTrue(lst.get(2).fst() == term.queryArgument(2));
    assertTrue(lst.get(3).snd().toString().equals("ε"));
    assertTrue(lst.get(3).fst() == term);
  }

  @Test
  public void testVisitor() {
    Type type = type("a -> b ->a");
    Variable z = new Binder("Z", type);
    Term arg1 = unaryTerm("g", type("a"), new Var("x", type("b")));
    Term arg2 = new Constant("c", type("b"));
    Application term = new Application(z, arg1, arg2);    // Z(g(x),c)
    ArrayList<String> parts = new ArrayList<String>();
    term.visitSubterms( (s,p) -> parts.add(s.toString()));
    assertTrue(parts.size() == 4);
    assertTrue(parts.get(0).equals("x"));
    assertTrue(parts.get(1).equals("g(x)"));
    assertTrue(parts.get(2).equals("c"));
    assertTrue(parts.get(3).equals("Z(g(x), c)"));
  }

  @Test
  public void testFullPositionsForBetaRedex() {
    Variable x = new Binder("x", type("A"));
    Constant a = new Constant("a", type("A"));
    Constant b = new Constant("b", type("B"));
    Constant f = new Constant("f", type("A -> B ->C"));
    Term term = new Application(new Abstraction(x, f.apply(x)), a, b); // (λx.f(x))(a, b)
    List<Position> lst = term.listPositions(false);
    assertTrue(lst.size() == 5);
    assertTrue(lst.get(0).toString().equals("0.1"));
    assertTrue(lst.get(1).toString().equals("0"));
    assertTrue(lst.get(2).toString().equals("1"));
    assertTrue(lst.get(3).toString().equals("2"));
    assertTrue(lst.get(4).toString().equals("ε"));
  }

  @Test
  public void testPartialPositions() {
    Type type = type("a -> b -> a");
    Variable z = new Binder("Z", type);
    Term arg1 = unaryTerm("g", type("a"), new Var("x", type("b")));
    Term arg2 = new Constant("c", type("b"));
    Term term = new Application(z, arg1, arg2);    // Z(g(x),c)
    List<Position> lst = term.listPositions(true);
    assertTrue(lst.size() == 7);
    assertTrue(lst.get(0).toString().equals("1.1"));
    assertTrue(lst.get(1).toString().equals("1.☆1"));
    assertTrue(lst.get(2).toString().equals("1"));
    assertTrue(lst.get(3).toString().equals("2"));
    assertTrue(lst.get(4).toString().equals("☆2"));
    assertTrue(lst.get(5).toString().equals("☆1"));
    assertTrue(lst.get(6).toString().equals("ε"));
  }

  @Test
  public void testFreeReplaceables() {
    // let's create: Z(Z(x,h(λz.c(z))),g(J[y],x)), where Z, x and y are variables and J is a
    // meta-variable
    Variable z = new Binder("Z", type("a -> b -> a"));
    FunctionSymbol g = new Constant("g", type("b -> a -> b"));
    FunctionSymbol c = new Constant("c", type("o -> o"));
    FunctionSymbol h = new Constant("h", type("(o -> o) -> b"));
    Variable x = new Binder("x", type("a"));
    Variable y = new Var("y", type("b"));
    Variable z2 = new Binder("z", type("o"));
    MetaVariable j = TermFactory.createMetaVar("J", type("b -> b"), 1);
    Term jy = TermFactory.createMeta(j, y);
    Term hlambdazcz = new Application(h, new Abstraction(z2, c.apply(z2)));
    Term s = new Application(z, new Application(z, x, hlambdazcz), new Application(g, jy, x));
    ReplaceableSet lst = s.queryFreeReplaceables();
    assertTrue(lst.contains(x));
    assertTrue(lst.contains(y));
    assertTrue(lst.contains(z));
    assertTrue(lst.contains(j));
    assertTrue(lst.size() == 4);
  }

  @Test
  public void testFreeReplaceablesReuse() {
    // let's create: f(g(x), h(y,y))
    Variable x = new Var("x", type("o"));
    Variable y = new Var("x", type("o"));
    Term gx = unaryTerm("g", type("o"), x);
    Term hyy = TermFactory.createConstant("h", 2).apply(y).apply(y);
    Term term = TermFactory.createConstant("f", 2).apply(gx).apply(hyy);
    assertTrue(gx.queryFreeReplaceables() == x.queryFreeReplaceables());
    assertTrue(hyy.queryFreeReplaceables() == y.queryFreeReplaceables());
    assertTrue(term.queryFreeReplaceables().size() == 2);
  }

  @Test
  public void testBoundVars() {
    // let's create: f(λx.Z(x), Y, g(λz.z, λx,u.h(x,y)))
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Variable z = new Binder("z", type("o"));
    Variable u = new Binder("u", type("o"));
    Variable bZ = new Var("Z", type("o -> o"));
    Variable bY = new Var("Y", type("o"));
    FunctionSymbol h = new Constant("h", type("o -> o -> o"));
    FunctionSymbol g = new Constant("g", type("(o -> o) -> (o -> o -> o) -> o"));
    FunctionSymbol f = new Constant("f",  type("(o -> o) -> o -> o -> o"));
    Term ahxy = new Abstraction(x, new Abstraction(u, new Application(h, x, y)));
    Term az = new Abstraction(z, z);
    Term gterm = new Application(g, az, ahxy);
    Term aZx = new Abstraction(x, new Application(bZ, x));
    Term fterm = new Application(f, aZx, bY).apply(gterm);

    ReplaceableSet freeVars = fterm.queryFreeReplaceables();
    ReplaceableSet boundVars = fterm.queryBoundVars();
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
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Variable bY = new Var("Y", type("o"));
    Constant f = new Constant("f", type("o -> o -> o"));
    Constant g = new Constant("g", type("(o -> o) -> o"));
    Constant h = new Constant("h", type("o -> (o -> o) -> o -> o"));
    Constant i = new Constant("i", type("(o -> o) -> (o -> o) -> o -> o"));
    Constant b = new Constant("B", type("o"));
    // let's create: (λxy.f(x,y))(g(λx.x), g(λy.y))
    Term ax = new Abstraction(x, x);
    Term gx = g.apply(ax);
    Term gy = g.apply(new Abstraction(y, y));
    Term head = new Abstraction(x, new Abstraction(y, new Application(f, x, y)));
    Term term1 = new Application(head, gx, gy);
    assertTrue(ax.queryBoundVars() == gx.queryBoundVars());
    assertTrue(term1.queryBoundVars() == head.queryBoundVars());
    // let's create: h(Y, λx.x, B)
    Term term2 = (new Application(h, bY, ax)).apply(b);
    assertTrue(term2.queryBoundVars() == ax.queryBoundVars());
    // let's create: i(λx.x, λy.f(g(λx.x), y))
    Term fterm = new Application(f, gx, y);
    Term afterm = new Abstraction(y, fterm);
    Term term3 = new Application(i, ax, afterm);
    assertTrue(term3.queryBoundVars() == afterm.queryBoundVars());
    assertFalse(afterm.queryBoundVars() == fterm.queryBoundVars());
  }

  @Test
  public void testMVars() {
    // let's create: a(f(Z[X], X), Y[b])
    Variable a = new Binder("a", type("o -> o -> o"));
    Variable b = new Binder("b", type("o"));
    Var x = new Var("Y", type("o"));
    MetaVariable y = TermFactory.createMetaVar("Y", type("o -> o"), 1);
    MetaVariable z = TermFactory.createMetaVar("Z", type("o -> o"), 1);
    Term zx = TermFactory.createMeta(z, x);
    Term f = new Constant("f", type("o -> o -> o"));
    Term fzxx = TermFactory.createApp(f, zx, x);
    Term yb = TermFactory.createMeta(y, b);
    Term term = TermFactory.createApp(a, fzxx, yb);
    // let's see if all the mvars are as expected!
    Environment<MetaVariable> mvars = term.queryMetaVariables();
    assertTrue(mvars.size() == 3);
    assertTrue(mvars.contains(x));
    assertTrue(mvars.contains(y));
    assertTrue(mvars.contains(z));
    mvars = fzxx.queryMetaVariables();
    assertTrue(mvars.size() == 2);
    assertTrue(mvars.contains(x));
    assertFalse(mvars.contains(y));
    assertTrue(mvars.contains(z));
    mvars = yb.queryMetaVariables();
    assertTrue(mvars.size() == 1);
  }

  @Test
  public void testTypeVars() {
    // let's create f(x_alpha, g(y_{d(beta)}, z_alpha)) :: gamma
    Type a = TypeFactory.createVariable("alpha");
    Type o = TypeFactory.createSort("o");
    Variable x = new Binder("x", a);
    Variable y = new Var("y", type("d($beta)"));
    Variable z = new Var("z", a);
    FunctionSymbol g = new Constant("g", type("d($beta) -> $alpha -> o"));
    FunctionSymbol f = new Constant("f", type("$alpha -> o -> $gamma"));
    Term gterm = new Application(g, y, z);
    Term fterm = new Application(f, x, gterm);
    TVarSet tvars = fterm.queryTypeVars();
    assertTrue(tvars.size() == 3);
    assertTrue(tvars.contains(TypeFactory.createVariable("alpha")));
    assertFalse(gterm.isMonomorphic());

    // what about (λu,v.k(f(u, v)))(x_alpha, g(y_{d(beta)}, z_alpha)) :: o?
    // (so the γ is hidden inside the head)
    Variable u = new Binder("u", a);
    Variable v = new Binder("v", o);
    Term sub = unaryTerm("k", o, new Application(f, u, v));
    Term abs = new Abstraction(u, new Abstraction(v, sub));
    Term appl = new Application(abs, x, gterm);
    tvars = appl.queryTypeVars();
    assertTrue(tvars.size() == 3);
    assertTrue(tvars.contains(TypeFactory.createVariable("gamma")));

    // check reuse as well
    FunctionSymbol h = new Constant("h", type("$alpha -> o -> o"));
    Term hterm = new Application(h, x, gterm);
    tvars = hterm.queryTypeVars();
    assertTrue(tvars.size() == 2);
    assertTrue(tvars == gterm.queryTypeVars());
  }

  @Test
  public void testFullSubtermGood() {
    Position p;
    Term s = twoArgFuncTerm();
    p = Position.empty;
    assertTrue(s.querySubterm(p).equals(s));
    p = new ArgumentPos(1, Position.empty);
    assertTrue(s.querySubterm(p).equals(new Constant("c", type("a"))));
    p = new ArgumentPos(2, new ArgumentPos(1, Position.empty));
    assertTrue(s.querySubterm(p).equals(new Constant("d", type("b"))));
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
    Variable x = new Binder("x", type("o"));
    Term s = new Application(new Abstraction(x, unaryTerm("f", type("o"), x)),
                             new Constant("a", type("o")));
    assertTrue(s.querySubterm(new LambdaPos(new ArgumentPos(1, Position.empty))) == x);
  }

  @Test
  public void testSubtermBad() {
    Term s = twoArgVarTerm();
    Position pos = new ArgumentPos(1, new ArgumentPos(2, Position.empty));
    assertThrows(InvalidPositionException.class, () -> s.querySubterm(pos));
  }

  @Test
  public void testHeadSubtermBad() {
    Term s = twoArgFuncTerm();
    Position pos = new ArgumentPos(2, new FinalPos(2));
    assertThrows(InvalidPositionException.class, () -> s.querySubterm(pos));
  }

  @Test
  public void testSubtermReplacementGood() {
    Variable z = new Var("Z", type("Int -> Int"));
    Term s = new Application(z, new Constant("37", type("Int")));
    Term t = s.replaceSubterm(new ArgumentPos(1, Position.empty), s);
    assertTrue(s.toString().equals("Z(37)"));
    assertTrue(t.queryArgument(1).equals(s));
    assertTrue(t.toString().equals("Z(Z(37))"));
  }

  @Test
  public void testSubtermInHeadReplacementGood() throws PositionFormatException {
    // (λxy.f(y,x))(a, b)
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Term f = new Constant("f", type("o -> o -> o"));
    Term a = new Constant("a", type("o"));
    Term b = new Constant("b", type("o"));
    Term s = new Application(new Abstraction(x, new Abstraction(y, new Application(f,y,x))), a, b);
    
    // replace y in f(y,x) by x
    Term t = s.replaceSubterm(Position.parse("0.0.1"), x);
    assertTrue(t.toString().equals("(λx.λy.f(x, x))(a, b)"));

    // replace f(y) by (λy.y)
    Term u = s.replaceSubterm(Position.parse("0.0.*1"), new Abstraction(y, y));
    assertTrue(u.toString().equals("(λx.λy.(λy__1.y__1)(x))(a, b)"));
  }

  @Test
  public void testSubtermHeadReplacementGood() {
    Term s = twoArgFuncTerm();  // f(c, g(d))
    Position pos = new ArgumentPos(2, new FinalPos(1));
    Term a = new Constant("a", type("A"));
    Variable x = new Binder("x", type("A -> b -> b"));
    Term t = s.replaceSubterm(pos, x.apply(a));
    assertTrue(t.toString().equals("f(c, x(a, d))"));
    Term q = t.replaceSubterm(pos, x.apply(a));
    assertTrue(t.equals(q));
    pos = new ArgumentPos(2, Position.empty);
    t = s.replaceSubterm(pos, new Constant("B", type("b")));
    assertTrue(t.toString().equals("f(c, B)"));
    assertTrue(s.toString().equals("f(c, g(d))"));
  }

  @Test
  public void testSubtermReplacementBadPosition() {
    Variable z = new Var("Z", type("Int -> Int"));
    Term s = new Application(z, new Constant("37", type("Int")));
    assertThrows(InvalidPositionException.class, () ->
      s.replaceSubterm(new ArgumentPos(2, Position.empty), s));
  }

  @Test
  public void testSubtermHeadReplacementBadPosition() {
    Variable z = new Var("Z", type("Int -> Int"));
    Term s = new Application(z, new Constant("37", type("Int")));
    assertThrows(InvalidPositionException.class, () ->
      s.replaceSubterm(new ArgumentPos(2, new FinalPos(1)), s));
  }

  @Test
  public void testSubtermHeadReplacementBadHeadPosition() {
    Constant f = new Constant("f", type("Int -> Int"));
    Term s = new Application(f, new Constant("37", type("Int")));
    assertThrows(InvalidPositionException.class, () ->
      s.replaceSubterm(new FinalPos(2), new Constant("a", type("B"))));
  }

  @Test
  public void testSubtermReplacementBadTypeSub() {
    Constant f = new Constant("f", type("Int -> Bool"));
    Term s = new Application(f, new Constant("37", type("Int")));
    assertThrows(TypingException.class, () ->
      s.replaceSubterm(new ArgumentPos(1, Position.empty), s));
  }

  @Test
  public void testSubtermReplacementBadTypeTop() {
    Variable z = new Binder("Z", type("Int -> Bool"));
    Term s = new Application(z, new Constant("37", type("Int")));
    assertThrows(TypingException.class, () ->
      s.replaceSubterm(Position.empty, new Constant("42", type("Int"))));
  }

  @Test
  public void testSubtermHeadReplacementBadType() {
    Variable z = new Binder("Z", type("Int -> Bool"));
    Term s = new Application(z, new Constant("37", type("Int")));
    Term replacement = new Constant("f", type("Int -> Int"));
    assertThrows(TypingException.class, () ->
      s.replaceSubterm(new FinalPos(1), replacement));
  }

  @Test
  public void testApplyingBaseTerm() {
    Term s = twoArgVarTerm();
    Term t = new Constant("37", type("Int"));
    assertThrows(TypingException.class, () -> s.apply(t));
  }

  @Test
  public void testApplyingBadType() {
    Type ty = type("a -> o -> a");
    Term c = new Constant("c", type("a"));
    FunctionSymbol f = new Constant("f", ty);
    Term fc = new Application(f, c);
    assertThrows(TypingException.class, () -> fc.apply(c));
  }

  @Test
  public void testCorrectApplication() {
    Type ty = type("a -> o -> a");
    Term c = new Constant("c", type("a -> a"));
    Term d = new Constant("d", type("a"));
    Variable x = new Var("x", ty);
    Term xc = new Application(x, c.apply(d));
    Term xcb = xc.apply(new Constant("b", type("o")));
    assertTrue(xcb.toString().equals("x(c(d), b)"));
  }

  @Test
  public void testRefreshBinders() {
    // (λxy.f(x,y))(g(λz.z), g(λz.z))
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("x", type("o"));
    Variable z = new Binder("x", type("o"));
    Term f = new Constant("f", type("o -> o -> o"));
    Term g = new Constant("g", type("(o -> o) -> o"));
    Term zz = new Abstraction(z, z);
    Term abs = new Abstraction(x, new Abstraction(y, new Application(f, x, y)));
    Term term = new Application(abs, new Application(g, zz), new Application(g, zz));

    TreeMap<Variable,Variable> map = new TreeMap<Variable,Variable>();
    map.put(y, new Var("y", type("o")));
    Term t = term.renameAndRefreshBinders(map);
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
    Variable x = new Binder("x", type("a"));
    Variable y = new Binder("y", type("b -> b"));
    Variable z = new Binder("z", type("c"));
    Term g = new Constant("g", type("(b -> b) -> a -> d"));
    Term f =
      new Constant("f", type("a -> ((b -> b) -> d) -> (a -> a) -> (c -> c) -> (b -> b) -> e"));
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
  public void testVarTermEquality() {
    Variable x = new Binder("x", type("o"));
    Variable y = new Var("y", type("o -> o -> o"));
    Variable x2 = new Binder("x2", type("o"));
    Term s1 = x;
    Term s2 = y;
    Term s3 = new Application(y, x);
    Term s4 = new Application(y, x, x);
    Term s5 = new Application(y, x, x);
    Term s6 = new Application(y, x, x2);
    
    assertTrue(s1.equals(s1));
    assertFalse(s1.equals(s2));
    assertFalse(s2.equals(s3));
    assertFalse(s3.equals(s4));
    assertFalse(s4.equals(s3));
    assertTrue(s4.equals(s5));
    assertFalse(s5.equals(s6));

    assertTrue(s4.hashCode() == s5.hashCode());
    TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
    mu.put(x, 3);
    assertTrue(s5.hashCode(mu) != s6.hashCode(mu));
    mu.put(x2, 3);
    assertTrue(s5.hashCode(mu) == s6.hashCode(mu));
  }

  @Test
  public void testFunctionalTermEquality() {
    Term s1 = new Constant("x", type("o"));
    Term s2 = unaryTerm("x", type("o"), new Constant("y", type("a")));
    Term s3 = unaryTerm("x", type("o"), new Constant("y", type("a")));
    Term s4 = unaryTerm("x", type("a"), new Constant("y", type("a")));
    assertFalse(s1.equals(s2));
    assertFalse(s2.equals(s1));
    assertTrue(s2.equals(s3));
    assertFalse(s2.equals(s4));
    assertFalse(s1.equals(new Var("x", type("o"))));
  }

  @Test
  public void testAlphaEquality() {
    // (λx.x) (f(y, λx.x)) =[y:=1,z:=1] (λy.y) (f(z, λx.x))
    Variable x = new Binder("x", type("o"));
    Variable y = new Binder("y", type("o"));
    Variable z = new Binder("z", type("o"));
    Constant f = new Constant("f", type("o -> (o -> o) -> o"));
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
    Variable a = new Binder("x", type("o -> o -> o"));
    Variable b = new Var("x", type("o"));
    Variable c = new Var("x", type("o"));
    Term combi = new Application(a, b, c);
    assertTrue(combi.toString().equals("x__3(x__1, x__2)"));
  }

  @Test
  public void testCorrectPrintingWithoundVariables() {
    // (λx0.x0)(f(g(x1, x2), λx3.g(x2, x3), λx4.λx3.g(x3,x4)))
    Variable x0 = new Binder("x", type("o"));
    Variable x1 = new Binder("x", type("o"));
    Variable x2 = new Binder("x", type("o"));
    Variable x3 = new Binder("x", type("o"));
    Variable x4 = new Binder("x", type("o"));
    Term g = new Constant("g", type("o -> o -> o"));
    Term f = new Constant("f", type("o -> (o -> o) -> (o -> o -> o) -> o"));
    Term abs = new Abstraction(x0,x0);
    Term arg1 = new Application(g, x1, x2);
    Term arg2 = new Abstraction(x3, new Application(g, x2, x3));
    Term arg3 = new Abstraction(x4, new Abstraction(x3, new Application(g, x3, x4)));
    Term total = new Application(abs, (new Application(f, arg1, arg2)).apply(arg3));
    assertTrue(total.toString().equals(
      "(λx__3.x__3)(f(g(x__1, x__2), λx__3.g(x__2, x__3), λx__3.λx__4.g(x__4, x__3)))"));
  }
}
