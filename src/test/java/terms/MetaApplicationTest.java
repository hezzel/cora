/**************************************************************************************************
 Copyright 2023 Cynthia Kop

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
import java.util.ArrayList;
import java.util.List;
import cora.exceptions.*;
import cora.types.Type;

public class MetaApplicationTest extends TermTestFoundation {
  @Test(expected = NullInitialisationError.class)
  public void testUnaryWithNullArg() {
    ArrayList<Type> inputs = new ArrayList<Type>();
    inputs.add(baseType("a"));
    MetaVariable z = new HigherMetaVar("z", inputs, baseType("b"));
    Term arg = null;
    Term t = TermFactory.createMeta(z, arg);
  }

  @Test(expected = NullInitialisationError.class)
  public void testBinaryWithNullHead() {
    TermFactory.createMeta(null, constantTerm("a", baseType("b")),
                                 constantTerm("a", baseType("c")));
  }

  @Test(expected = NullInitialisationError.class)
  public void testNullArgs() {
    ArrayList<Type> inputs = new ArrayList<Type>();
    inputs.add(baseType("a"));
    MetaVariable z = new HigherMetaVar("z", inputs, baseType("b"));
    ArrayList<Term> args = null;
    TermFactory.createMeta(z, args);
  }

  @Test(expected = ArityError.class)
  public void testNotEnoughArgs() {
    ArrayList<Type> inputs = new ArrayList<Type>();
    inputs.add(baseType("a"));
    inputs.add(baseType("a"));
    inputs.add(baseType("a"));
    MetaVariable z = new HigherMetaVar("z", inputs, baseType("a"));
    Term s = constantTerm("s", baseType("a"));
    TermFactory.createMeta(z, s, s);
  }

  @Test(expected = ArityError.class)
  public void testTooManyArgs() {
    ArrayList<Type> inputs = new ArrayList<Type>();
    inputs.add(baseType("a"));
    inputs.add(baseType("a"));
    MetaVariable z = new HigherMetaVar("z", inputs, arrowType("a", "a"));
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(constantTerm("a", baseType("a")));
    args.add(constantTerm("a", baseType("a")));
    args.add(constantTerm("a", baseType("a")));
    TermFactory.createMeta(z, args);
  }

  @Test(expected = IllegalTermError.class)
  public void testNoArgs() {
    MetaVariable z = new Var("z", arrowType("a", "a"));
    ArrayList<Term> args = new ArrayList<Term>();
    new MetaApplication(z, args);
  }

  @Test
  public void testNoArgsBecomesVar() {
    MetaVariable z = new Var("z", arrowType("a", "a"));
    ArrayList<Term> args = new ArrayList<Term>();
    Term t = TermFactory.createMeta(z, args);
    assertTrue(t == z);
  }
  
  @Test(expected = TypingError.class)
  public void testBadArgumentType() {
    ArrayList<Type> inputs = new ArrayList<Type>();
    inputs.add(baseType("a"));
    inputs.add(baseType("a"));
    MetaVariable z = new HigherMetaVar("z", inputs, arrowType("a", "a"));
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(constantTerm("a", baseType("a")));
    args.add(constantTerm("b", baseType("b")));
    TermFactory.createMeta(z, args);
  }

  private Term makeMeta(String name, Term arg, Type output) {
    ArrayList<Type> inputs = new ArrayList<Type>();
    inputs.add(arg.queryType());
    MetaVariable z = new HigherMetaVar(name, inputs, output);
    return TermFactory.createMeta(z, arg);
  }

  private Term makeMeta(String name, Term arg1, Term arg2, Type output) {
    ArrayList<Type> inputs = new ArrayList<Type>();
    inputs.add(arg1.queryType());
    inputs.add(arg2.queryType());
    MetaVariable z = new HigherMetaVar(name, inputs, output);
    return TermFactory.createMeta(z, arg1, arg2);
  }

  private Term makeSample() {
    // create: Z[f(x), λy.f(y)]
    Variable x = TermFactory.createVar("x", baseType("A"));
    Variable y = TermFactory.createBinder("y", baseType("A"));
    Term arg1 = unaryTerm("f", baseType("B"), x);
    Term arg2 = TermFactory.createAbstraction(y, unaryTerm("f", baseType("B"), y));
    return makeMeta("Z", arg1, arg2, baseType("A"));
  }

  @Test
  public void testSingleVariableSets() {
    // create: Z[f(x), λy.f(y)]
    Variable x = TermFactory.createVar("x", baseType("A"));
    Variable y = TermFactory.createBinder("y", baseType("A"));
    Term arg1 = unaryTerm("f", baseType("B"), x);
    Term arg2 = unaryTerm("g", baseType("C"),
      TermFactory.createAbstraction(y, unaryTerm("f", baseType("B"), y)));
    Term s = makeMeta("Z", arg1, arg2, baseType("A"));
    // no merging needed => no creation of new free variable set needed
    assertTrue(s.vars() == arg1.vars());
    // no merging or renaming needed => bound variable set also stays the same
    assertTrue(s.boundVars() == arg2.boundVars());
  }

  @Test
  public void testProperlyMergeVariableSets() {
    // create: H[Z[x, Z[f(x, λu.u), g(y)]], f(z, λu.u)]
    Variable x = TermFactory.createVar("x", baseType("B"));
    Variable y = TermFactory.createVar("y", baseType("Y"));
    Variable z = TermFactory.createVar("z", baseType("B"));
    Variable u = TermFactory.createBinder("u", baseType("U"));
    FunctionSymbol f = TermFactory.createConstant("f", arrowType(baseType("B"),
      arrowType(arrowType("U", "U"), baseType("B"))));
    Term abs = TermFactory.createAbstraction(u, u);
    Term fabs = TermFactory.createApp(f, x, abs);
    Term gy = unaryTerm("g", baseType("A"), y);
    ArrayList<Type> inputs = new ArrayList<Type>();
    inputs.add(baseType("B"));
    inputs.add(baseType("A"));
    MetaVariable m = new HigherMetaVar("Z", inputs, baseType("A"));
    Term sub1 = TermFactory.createMeta(m, fabs, gy);
    Term sub2 = TermFactory.createMeta(m, x, sub1);
    Term sub3 = TermFactory.createApp(f, z, abs);
    Term top = makeMeta("H", sub2, sub3, baseType("C"));

    // in Z[f(x, λu.u), g(y)], the free variable sets are merged
    assertTrue(sub1.vars().size() == 2);
    assertTrue(sub1.vars().contains(x));
    assertTrue(sub1.vars().contains(y));
    assertFalse(sub1.vars().contains(u));
    // in Z[x, Z[f(x, λu.u), g(y)]], no additional merging needs to happen
    assertTrue(sub1.vars() == sub2.vars());
    // but in the top term, we have a merged set again
    assertTrue(top.vars().size() == 3);
    assertTrue(top.vars().contains(x));
    assertTrue(top.vars().contains(y));
    assertTrue(top.vars().contains(z));
    // as for the bound variable sets, no renaming or merging is done
    assertTrue(top.boundVars() == abs.boundVars());

    // create: H[Z[x, Z[f(x, λu.u), g(y)]], f(z, λu'.u')]
    Variable v = TermFactory.createBinder("u", baseType("U"));
    Term abs2 = TermFactory.createAbstraction(v, v);
    Term sub3alter = TermFactory.createApp(f, z, abs2);
    Term topalter = makeMeta("H", sub2, sub3alter, baseType("C"));
    assertTrue(topalter.boundVars().size() == 2);
    assertTrue(topalter.boundVars().contains(u));
    assertTrue(topalter.boundVars().contains(v));
  }

  @Test
  public void testBasics() {
    Term t = makeSample();
    assertTrue(t.queryType().equals(baseType("A")));
    assertFalse(t.isConstant());
    assertFalse(t.isVariable());
    assertFalse(t.isAbstraction());
    assertFalse(t.isApplication());
    assertTrue(t.isMetaApplication());
    assertFalse(t.isFunctionalTerm());
    assertFalse(t.isVarTerm());
    assertFalse(t.isBetaRedex());
    assertFalse(t.isApplicative());
    assertFalse(t.isFirstOrder());
    assertFalse(t.isPattern());
    assertTrue(t.numberArguments() == 0);
    assertTrue(t.queryArguments().size() == 0);
    assertTrue(t.queryHead() == t);
    assertTrue(t.queryImmediateHeadSubterm(0) == t);
    assertTrue(t.toString().equals("Z⟨f(x), λy.f(y)⟩"));
    assertTrue(t.queryMetaVariable().toString().equals("Z"));
    Term q = null;
    assertFalse(t.equals(q));
  }

  @Test
  public void testMetaArguments() {
    // create: Z[f(x), λy.f(y)]
    Variable x = TermFactory.createVar("x", baseType("A"));
    Variable y = TermFactory.createBinder("y", baseType("A"));
    Term arg1 = unaryTerm("f", baseType("B"), x);
    Term arg2 = TermFactory.createAbstraction(y, unaryTerm("f", baseType("B"), y));
    Term t = makeMeta("Z", arg1, arg2, baseType("A"));
    assertTrue(t.queryMetaVariable().queryArity() == 2);
    assertTrue(t.queryMetaArgument(1) == arg1);
    assertTrue(t.queryMetaArgument(2) == arg2);
  }

  @Test
  public void testPattern() {
    ArrayList<Type> inputs = new ArrayList<Type>();
    for (int i = 0; i < 3; i++) inputs.add(baseType("A"));
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(TermFactory.createBinder("x", baseType("A")));
    args.add(TermFactory.createBinder("y", baseType("A")));
    args.add(TermFactory.createBinder("z", baseType("A")));
    MetaVariable z = new HigherMetaVar("mvar", inputs, baseType("B"));
    Term t = TermFactory.createMeta(z, args);
    assertTrue(t.isPattern());
    assertFalse(t.isFirstOrder());
    args.set(2, args.get(0));
    assertTrue(t.isPattern());
    Term s = TermFactory.createMeta(z, args);
    assertFalse(s.isPattern());
  }

  @Test(expected = IndexingError.class)
  public void testImmediateHeadSubterm() {
    Term t = makeSample();
    t.queryImmediateHeadSubterm(1);
  }

  @Test(expected = IndexingError.class)
  public void testArgument() {
    Term t = makeSample();
    t.queryArgument(1);
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testRoot() {
    Term t = makeSample();
    t.queryRoot();
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testVariable() {
    Term t = makeSample();
    t.queryVariable();
  }

  @Test
  public void testAppliedMetaApp() {
    Variable x = TermFactory.createBinder("x", baseType("o"));
    Variable y = TermFactory.createBinder("x", baseType("a"));
    Variable z = TermFactory.createBinder("z", baseType("a"));
    ArrayList<Type> inputs = new ArrayList<Type>();
    inputs.add(baseType("o"));
    Type output = arrowType(baseType("a"), arrowType("a", "b"));
    MetaVariable m = new HigherMetaVar("Z", inputs, output);
    Term zx = TermFactory.createMeta(m, x);
    Term total = TermFactory.createApp(zx, y, z);
    assertTrue(total.toString().equals("Z⟨x__1⟩(x__2, z)"));
  }

  @Test
  public void testAlphaEquality() {
    // M[λx.x, λx.f(x), u]
    Variable x = TermFactory.createBinder("x", baseType("o"));
    Variable y = TermFactory.createBinder("y", baseType("o"));
    Variable z = TermFactory.createBinder("z", baseType("o"));
    Variable u = TermFactory.createBinder("u", baseType("o"));
    Type o = baseType("o");
    Term fx = unaryTerm("f", o, x);
    ArrayList<Type> inputs = new ArrayList<Type>();
    inputs.add(arrowType("o", "o"));
    inputs.add(arrowType("o", "o"));
    inputs.add(baseType("o"));
    MetaVariable m = new HigherMetaVar("M", inputs, baseType("o"));
    ArrayList<Term> args1 = new ArrayList<Term>();
    args1.add(TermFactory.createAbstraction(x, x));
    args1.add(TermFactory.createAbstraction(x, unaryTerm("f", o, x)));
    args1.add(u);
    Term s = TermFactory.createMeta(m, args1);
    ArrayList<Term> args2 = new ArrayList<Term>();
    args2.add(TermFactory.createAbstraction(y, y));
    args2.add(TermFactory.createAbstraction(z, unaryTerm("f", o, z)));
    args2.add(u);
    Term t = TermFactory.createMeta(m, args1);
    assertTrue(s.equals(t));
    assertTrue(t.equals(s));
  }

  /** @return Z⟨g(x),c⟩ :: a ⇒ b */
  private Term createTestTerm() {
    Type type = arrowType(baseType("a"), arrowType(baseType("b"), arrowType("a", "b")));
    MetaVariable z = TermFactory.createMetaVar("Z", type, 2);
    Term arg1 = unaryTerm("g", baseType("a"), new Var("x", baseType("b")));
    Term arg2 = constantTerm("c", baseType("b"));
    return TermFactory.createMeta(z, arg1, arg2);
  }

  @Test
  public void testPositions() {
    Term term = createTestTerm();
    List<Path> lst = term.queryPositions();
    assertTrue(lst.size() == 4);
    assertTrue(lst.get(0).toString().equals("!1.1.ε"));
    assertTrue(lst.get(1).toString().equals("!1.ε"));
    assertTrue(lst.get(2).toString().equals("!2.ε"));
    assertTrue(lst.get(3).toString().equals("ε"));
    assertTrue(lst.get(1).queryAssociatedTerm() == term);
    assertTrue(lst.get(2).queryCorrespondingSubterm() == term.queryMetaArgument(2));
    assertTrue(lst.get(3).queryCorrespondingSubterm() == term);
  }

  @Test
  public void testPositionsForHead() {
    Term term = createTestTerm();
    List<Path> lst = term.queryPositionsForHead(term);
    assertTrue(lst.size() == 3);
    assertTrue(lst.get(0).toString().equals("!1.1.ε"));
    assertTrue(lst.get(1).toString().equals("!1.ε"));
    assertTrue(lst.get(2).toString().equals("!2.ε"));
    assertTrue(lst.get(1).queryAssociatedTerm() == term);
    assertTrue(lst.get(2).queryCorrespondingSubterm() == term.queryMetaArgument(2));
  }

  @Test
  public void testPositionsInApplication() {
    Term term = createTestTerm().apply(constantTerm("a", baseType("a")));
    List<Path> lst = term.queryPositions();
    assertTrue(lst.size() == 5);
    assertTrue(lst.get(0).toString().equals("!1.1.ε"));
    assertTrue(lst.get(1).toString().equals("!1.ε"));
    assertTrue(lst.get(2).toString().equals("!2.ε"));
    assertTrue(lst.get(3).toString().equals("1.ε"));
    assertTrue(lst.get(4).toString().equals("ε"));
    assertTrue(lst.get(1).queryAssociatedTerm() == term);
    assertTrue(lst.get(2).queryCorrespondingSubterm() == term.queryMetaArgument(2));
  }

  @Test
  public void testHeadPositions() {
    Term term = createTestTerm().apply(constantTerm("a", baseType("a")));
    List<HeadPosition> lst = term.queryHeadPositions();
    assertTrue(lst.size() == 7);
    assertTrue(lst.get(0).toString().equals("!1.1.ε"));   // Z⟨g([]),c⟩(a)
    assertTrue(lst.get(1).toString().equals("!1.☆1"));    // Z⟨[](x),c⟩(a)
    assertTrue(lst.get(2).toString().equals("!1.ε"));     // Z⟨[],c⟩(a)
    assertTrue(lst.get(3).toString().equals("!2.ε"));     // Z⟨g(x),[]⟩(a)
    assertTrue(lst.get(4).toString().equals("1.ε"));      // Z⟨g(x),c⟩([])
    assertTrue(lst.get(5).toString().equals("☆1"));       // [](a)
    assertTrue(lst.get(6).toString().equals("ε"));        // []
  }

  @Test
  public void testSubtermGood() {
    // term Z⟨g(x),c⟩(a)
    Term term = createTestTerm().apply(constantTerm("a", baseType("a")));
    // position !1.1
    Position pos = new ConsPosition(-1, new ConsPosition(1, new EmptyPosition()));
    assertTrue(term.querySubterm(pos) instanceof Var);
  }

  @Test
  public void testHeadSubtermGood() {
    // term Z⟨g(x),c⟩
    Term term = createTestTerm();
    // position !1.☆1
    HeadPosition pos = new HeadPosition(new ConsPosition(-1, new EmptyPosition()), 1);
    assertTrue(term.querySubterm(pos).toString().equals("g"));
  }

  @Test(expected = IndexingError.class)
  public void testSubtermBad() {
    Term term = createTestTerm();
    Position pos = PositionFactory.createArg(1,PositionFactory.empty);
    Term t = term.querySubterm(pos);
  }

  @Test(expected = IndexingError.class)
  public void testHeadSubtermBad() {
    Term term = createTestTerm();
    HeadPosition pos = new HeadPosition(PositionFactory.empty, 1);
    term.querySubterm(pos);
  }

  @Test
  public void testSubtermReplacementGood() {
    Term term = createTestTerm();
    Position pos =
      PositionFactory.createMeta(1, PositionFactory.createArg(1, PositionFactory.empty));
    Term replacement = constantTerm("42", baseType("b"));
    Term s = term.replaceSubterm(pos, replacement);
    assertTrue(s.toString().equals("Z⟨g(42), c⟩"));
    assertTrue(term.toString().equals("Z⟨g(x), c⟩"));
  }

  @Test
  public void testHeadSubtermReplacementGood() {
    // term Z⟨g(x),c⟩(a)
    Term term = createTestTerm().apply(constantTerm("a", baseType("a")));
    // replacement λx.a
    Variable x = new Binder("x", baseType("b"));
    Term replacement = new Abstraction(x, constantTerm("a", baseType("a")));
    // position !1.☆1
    HeadPosition pos = new HeadPosition(new ConsPosition(-1, new EmptyPosition()), 1);
    // replacement Z⟨(λx1.a)(x),c⟩(a)
    Term s = term.replaceSubterm(pos, replacement);
    assertTrue(s.toString().equals("Z⟨(λx1.a)(x), c⟩(a)"));
  }

  @Test(expected = IndexingError.class)
  public void testSubtermReplacementBadPositionType() {
    Term term = createTestTerm();
    Position pos = PositionFactory.parsePos("2.ε");
    Term replacement = constantTerm("uu", baseType("b"));
    term.replaceSubterm(pos, replacement);
  }

  @Test(expected = IndexingError.class)
  public void testSubtermReplacementBadPositionRange() {
    Term term = createTestTerm();
    HeadPosition pos = PositionFactory.parseHPos("!3.ε");
    Term replacement = constantTerm("uu", baseType("b"));
    term.replaceSubterm(pos, replacement);
  }

  @Test(expected = IndexingError.class)
  public void testSubtermReplacementBadHeadPosition() {
    Term term = createTestTerm();
    HeadPosition pos = PositionFactory.parseHPos("☆1");
    Term replacement = constantTerm("uu", arrowType("a", "b"));
    term.replaceSubterm(pos, replacement);
  }

  @Test(expected = TypingError.class)
  public void testSubtermReplacementBadType() {
    Term term = createTestTerm();
    Position pos = PositionFactory.empty;
    Term replacement = constantTerm("uu", baseType("x"));
    term.replaceSubterm(pos, replacement);
  }

  /*
  @Test(expected = IndexingError.class)
  public void testSubtermReplacementBadPosition() {
    Variable z = new Var("Z", arrowType("Int", "Int"));
    Term s = new Application(z, constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(PositionFactory.createArg(2, PositionFactory.empty), s);
  }

  @Test(expected = IndexingError.class)
  public void testSubtermHeadReplacementBadPosition() {
    Variable z = new Var("Z", arrowType("Int", "Int"));
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
    Variable z = new Binder("Z", arrowType("Int", "Bool"));
    Term s = new Application(z, constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(PositionFactory.empty, constantTerm("42", baseType("Int")));
  }

  @Test(expected = TypingError.class)
  public void testSubtermHeadReplacementBadType() {
    Variable z = new Binder("Z", arrowType("Int", "Bool"));
    Term s = new Application(z, constantTerm("37", baseType("Int")));
    Term replacement = constantTerm("f", arrowType("Int", "Int"));
    s.replaceSubterm(new HeadPosition(PositionFactory.empty, 1), replacement);
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
    Term t = twoArgFuncTerm();
    Term f = t.queryAbstractionSubterm();
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
    args.set(1, z.apply(ba));
    Term combiterm = new Application(x, args);  // x(y, bb(aa), z(bb(aa)))
    assertFalse(combiterm.isPattern()); // but the arguments do all need to be patterns :)
  }

  @Test
  public void testFreeVars() {
    // let's create: Z(Z(x,h(λz.c(z))),g(y,x)), where Z, x and y are variables
    Variable z = new Binder("Z", arrowType(baseType("a"),arrowType("b","a")));
    FunctionSymbol g = new Constant("g", arrowType(baseType("b"),arrowType("a","b")));
    FunctionSymbol c = new Constant("c", arrowType("o", "o"));
    FunctionSymbol h = new Constant("h", arrowType(arrowType("o", "o"), baseType("b")));
    Variable x = new Binder("x", baseType("a"));
    Variable y = new Var("y", baseType("b"));
    Variable z2 = new Binder("z", baseType("o"));
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
    Variable x = new Var("x", baseType("o"));
    Variable y = new Var("x", baseType("o"));
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

  @Test(expected = NullCallError.class)
  public void testNullMatch() {
    Term t = twoArgFuncTerm();
    Substitution subst = new Subst();
    t.match(null, subst);
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
    TreeMap<Variable,String> naming = new TreeMap<Variable,String>();
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
*/
}
