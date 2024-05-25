/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

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
import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;
import charlie.exceptions.*;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.position.*;

class MetaApplicationTest extends TermTestFoundation {
  @Test
  public void testUnaryWithNullArg() {
    MetaVariable z = TermFactory.createMetaVar("z", baseType("a"), baseType("b"));
    Term arg = null;
    assertThrows(java.lang.NullPointerException.class, () -> TermFactory.createMeta(z, arg));
  }

  @Test
  public void testBinaryWithNullHead() {
    assertThrows(NullInitialisationError.class, () ->
      TermFactory.createMeta(null, constantTerm("a", baseType("b")),
                                   constantTerm("a", baseType("c"))));
  }

  @Test
  public void testNullArgs() {
    MetaVariable z = TermFactory.createMetaVar("z", baseType("a"), baseType("b"));
    ArrayList<Term> args = null;
    assertThrows(NullInitialisationError.class, () -> TermFactory.createMeta(z, args));
  }

  @Test
  public void testIncorrectArgsCount() {
    ArrayList<Type> inputs = new ArrayList<Type>();
    inputs.add(baseType("a"));
    inputs.add(baseType("a"));
    inputs.add(baseType("a"));
    MetaVariable z = TermFactory.createMetaVar("z", inputs, baseType("a"));
    Term s = constantTerm("s", baseType("a"));
    assertThrows(ArityException.class, () -> TermFactory.createMeta(z, s, s));
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(constantTerm("a", baseType("a")));
    args.add(constantTerm("a", baseType("a")));
    args.add(constantTerm("a", baseType("a")));
    args.add(constantTerm("a", baseType("a")));
    assertThrows(ArityException.class, () -> TermFactory.createMeta(z, args));
  }

  @Test
  public void testNoArgs() {
    MetaVariable z = new Var("z", arrowType("a", "a"));
    ArrayList<Term> args = new ArrayList<Term>();
    assertThrows(IllegalTermError.class, () -> new MetaApplication(z, args));
  }

  @Test
  public void testBadArgumentType() {
    ArrayList<Type> inputs = new ArrayList<Type>();
    inputs.add(baseType("a"));
    inputs.add(baseType("a"));
    MetaVariable z = TermFactory.createMetaVar("z", inputs, arrowType("a", "a"));
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(constantTerm("a", baseType("a")));
    args.add(constantTerm("b", baseType("b")));
    assertThrows(TypingError.class, () -> TermFactory.createMeta(z, args));
  }

  @Test
  public void testNoArgsBecomesVar() {
    MetaVariable z = new Var("z", arrowType("a", "a"));
    ArrayList<Term> args = new ArrayList<Term>();
    Term t = TermFactory.createMeta(z, args);
    assertTrue(t == z);
  }

  private Term makeMeta(String name, Term arg, Type output) {
    ImmutableList<Type> inputs = ImmutableList.<Type>builder().add(arg.queryType()).build();
    MetaVariable z = new HigherMetaVar(name, inputs, output);
    return TermFactory.createMeta(z, arg);
  }

  private Term makeMeta(String name, Term arg1, Term arg2, Type output) {
    MetaVariable z = TermFactory.createMetaVar(name, arg1.queryType(), arg2.queryType(), output);
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
    assertTrue(t.isClosed());   // Z is not a binder
    assertFalse(t.isGround());
    assertFalse(t.isTrueTerm());
    assertTrue(t.numberArguments() == 0);
    assertTrue(t.numberMetaArguments() == 2);
    assertTrue(t.queryArguments().size() == 0);
    assertTrue(t.queryMetaArguments().size() == 2);
    assertTrue(t.queryMetaArguments().get(0).toString().equals("f(x)"));
    assertTrue(t.queryHead() == t);
    assertTrue(t.queryImmediateHeadSubterm(0) == t);
    assertTrue(t.toString().equals("Z⟨f(x), λy.f(y)⟩"));
    assertTrue(t.queryMetaVariable().toString().equals("Z"));
    Term q = null;
    assertFalse(t.equals(q));
  }

  @Test
  public void testStore() {
    TreeSet<FunctionSymbol> set = new TreeSet<FunctionSymbol>();
    Term t = makeSample();
    t.storeFunctionSymbols(set);
    assertTrue(set.size() == 1);
    assertTrue(set.toString().equals("[f]"));
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
    // no variable merging needed, but we still need to create a new free replaceable set due to
    // the addition of the meta-variable
    assertTrue(arg1.freeReplaceables().size() == 1);
    assertTrue(s.freeReplaceables().size() == 2);
    // bound variable set stays the same, however
    assertTrue(s.boundVars() == arg2.boundVars());
  }

  @Test
  public void testProperlyMergeReplaceableSets() {
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
    MetaVariable m = TermFactory.createMetaVar("Z", baseType("B"), baseType("A"), baseType("A"));
    Term sub1 = TermFactory.createMeta(m, fabs, gy);
    Term sub2 = TermFactory.createMeta(m, x, sub1);
    Term sub3 = TermFactory.createApp(f, z, abs);
    Term top = makeMeta("H", sub2, sub3, baseType("C"));

    // in Z[f(x, λu.u), g(y)], the free replaceable sets are merged and Z is added
    assertTrue(sub1.freeReplaceables().contains(m));
    assertTrue(sub1.freeReplaceables().size() == 3);
    assertTrue(sub1.freeReplaceables().contains(x));
    assertTrue(sub1.freeReplaceables().contains(y));
    assertFalse(sub1.freeReplaceables().contains(u));
    // in Z[x, Z[f(x, λu.u), g(y)]], no additional merging needs to happen
    assertTrue(sub1.freeReplaceables() == sub2.freeReplaceables());
    // but in the top term, we have a merged set again
    assertTrue(top.freeReplaceables().size() == 5);
    assertTrue(top.freeReplaceables().contains(x));
    assertTrue(top.freeReplaceables().contains(y));
    assertTrue(top.freeReplaceables().contains(z));
    assertTrue(sub1.freeReplaceables().contains(m));
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
  public void testMetaApplicationCannotBeGround() {
    Term t = makeMeta("Z", constantTerm("a", baseType("o")), baseType("o"));
    assertFalse(t.isGround());
    assertTrue(t.isClosed());
  }

  @Test
  public void testTheory() {
    // X[0] with X :: Int → a
    Term zero = new IntegerValue(0);
    Term s = makeMeta("X", zero, baseType("a"));
    assertFalse(s.isTheoryTerm());
    assertFalse(s.isValue());

    // Y[o] with Y :: Int → Int but o not a theory term
    Type i = zero.queryType();
    s = makeMeta("Y", new Constant("o", i), i);
    assertFalse(s.isTheoryTerm());
    assertTrue(s.toValue() == null);

    // Z[λx.x,y] with Z :: (Int → Int) → String → Bool
    Variable x = new Binder("x", i);
    Variable y = new Var("y", TypeFactory.stringSort);
    Term abs = new Abstraction(x, x);
    s = makeMeta("Z", abs, y, TypeFactory.boolSort);
    assertTrue(s.isTheoryTerm());
    assertFalse(s.isValue());
    assertTrue(s.toValue() == null);
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
    MetaVariable z = TermFactory.createMetaVar("mvar", inputs, baseType("B"));
    Term t = TermFactory.createMeta(z, args);
    assertTrue(t.isPattern());
    assertFalse(t.isFirstOrder());
    args.set(2, args.get(0));
    assertTrue(t.isPattern());
    Term s = TermFactory.createMeta(z, args);
    assertFalse(s.isPattern());
  }

  /** @return Z⟨g(x),c⟩ :: a → b */
  private Term createTestTerm() {
    Type type = arrowType(baseType("a"), arrowType(baseType("b"), arrowType("a", "b")));
    MetaVariable z = TermFactory.createMetaVar("Z", type, 2);
    Term arg1 = unaryTerm("g", baseType("a"), new Var("x", baseType("b")));
    Term arg2 = constantTerm("c", baseType("b"));
    return TermFactory.createMeta(z, arg1, arg2);
  }

  @Test
  public void testSubterms() {
    Term term = createTestTerm();
    List<Pair<Term,Position>> lst = term.querySubterms();
    assertTrue(lst.size() == 4);
    assertTrue(lst.get(0).snd().toString().equals("!1.1.ε"));
    assertTrue(lst.get(1).snd().toString().equals("!1.ε"));
    assertTrue(lst.get(2).fst() == term.queryMetaArgument(2));
    assertTrue(lst.get(2).snd().toString().equals("!2.ε"));
    assertTrue(lst.get(3).fst() == term);
    assertTrue(lst.get(3).snd().toString().equals("ε"));
    assertTrue(term.hasSubterm(lst.get(0).fst()));
  }

  @Test
  public void testSubtermsInApplication() {
    Term term = createTestTerm().apply(constantTerm("a", baseType("a")));
    List<Pair<Term,Position>> lst = term.querySubterms();
    assertTrue(lst.size() == 5);
    assertTrue(lst.get(0).snd().toString().equals("!1.1.ε"));
    assertTrue(lst.get(1).snd().toString().equals("!1.ε"));
    assertTrue(lst.get(2).fst() == term.queryMetaArgument(2));
    assertTrue(lst.get(2).snd().toString().equals("!2.ε"));
    assertTrue(lst.get(3).snd().toString().equals("1.ε"));
    assertTrue(lst.get(4).snd().toString().equals("ε"));
    assertTrue(term.hasSubterm(lst.get(3).fst()));
    assertTrue(term.hasSubterm(lst.get(4).fst()));
    assertFalse(term.hasSubterm(TermFactory.createVar("x", baseType("b"))));
  }

  @Test
  public void testPartialPositions() {
    Term term = createTestTerm().apply(constantTerm("a", baseType("a")));
    List<Position> lst = term.queryPositions(true);
    assertTrue(lst.size() == 7);
    assertTrue(lst.get(0).toString().equals("!1.1.ε"));   // x
    assertTrue(lst.get(1).toString().equals("!1.☆1"));    // g
    assertTrue(lst.get(2).toString().equals("!1.ε"));     // g(x)
    assertTrue(lst.get(3).toString().equals("!2.ε"));     // c
    assertTrue(lst.get(4).toString().equals("1.ε"));      // a
    assertTrue(lst.get(5).toString().equals("☆1"));       // Z⟨g(x),c⟩
    assertTrue(lst.get(6).toString().equals("ε"));        // Z⟨g(x),c⟩(a)
  }

  @Test
  public void testSubtermGood() {
    // term Z⟨g(x),c⟩(a)
    Term term = createTestTerm().apply(constantTerm("a", baseType("a")));
    // position !1.1
    Position pos = new MetaPos(1, new ArgumentPos(1, new FinalPos(0)));
    assertTrue(term.querySubterm(pos) instanceof Var);
  }

  @Test
  public void testHeadSubtermGood() {
    // term Z⟨g(x),c⟩
    Term term = createTestTerm();
    // position !1.☆1
    Position pos = new MetaPos(1, new FinalPos(1));
    assertTrue(term.querySubterm(pos).toString().equals("g"));
  }

  @Test
  public void testSubtermBad() {
    Term term = createTestTerm();
    Position pos = new ArgumentPos(1, Position.empty);
    assertThrows(IndexingError.class, () -> term.querySubterm(pos));
  }

  @Test
  public void testHeadSubtermBad() {
    Term term = createTestTerm();
    Position pos = new FinalPos(1);
    assertThrows(IndexingError.class, () -> term.querySubterm(pos));
  }

  @Test
  public void testSubtermReplacementGood() {
    Term term = createTestTerm();
    Position pos = Position.parse("!1.1");
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
    Position pos = new MetaPos(1, new FinalPos(1));
    // replacement Z⟨(λx1.a)(x),c⟩(a)
    Term s = term.replaceSubterm(pos, replacement);
    assertTrue(s.toString().equals("Z⟨(λx1.a)(x), c⟩(a)"));
  }

  @Test
  public void testSubtermReplacementBadPositionKind() {
    Term term = createTestTerm();
    Position pos = Position.parse("2.ε");
    Term replacement = constantTerm("uu", baseType("b"));
    assertThrows(IndexingError.class, () -> term.replaceSubterm(pos, replacement));
  }

  @Test
  public void testSubtermReplacementBadPositionRange() {
    Term term = createTestTerm();
    Position pos = Position.parse("!3.ε");
    Term replacement = constantTerm("uu", baseType("b"));
    assertThrows(IndexingError.class, () -> term.replaceSubterm(pos, replacement));
  }

  @Test
  public void testSubtermReplacementBadHeadPosition() {
    Term term = createTestTerm();
    Position pos = Position.parse("☆1");
    Term replacement = constantTerm("uu", arrowType("a", "b"));
    assertThrows(IndexingError.class, () -> term.replaceSubterm(pos, replacement));
  }

  @Test
  public void testSubtermReplacementBadType() {
    Term term = createTestTerm();
    Position pos = Position.empty;
    Term replacement = constantTerm("uu", baseType("x"));
    assertThrows(TypingError.class, () -> term.replaceSubterm(pos, replacement));
  }

  @Test
  public void testIllegalCalls() {
    Term t = makeSample();
    assertThrows(IndexingError.class, () -> t.queryImmediateHeadSubterm(1));
    assertThrows(IndexingError.class, () -> t.queryArgument(1));
    assertThrows(InappropriatePatternDataError.class, () -> t.queryRoot());
    assertThrows(InappropriatePatternDataError.class, () -> t.queryVariable());
  }

  @Test
  public void testAppliedMetaApp() {
    Variable x = TermFactory.createBinder("x", baseType("o"));
    Variable y = TermFactory.createBinder("x", baseType("a"));
    Variable z = TermFactory.createBinder("z", baseType("a"));
    Type output = arrowType(baseType("a"), arrowType("a", "b"));
    MetaVariable m = TermFactory.createMetaVar("Z", baseType("o"), output);
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
    MetaVariable m = TermFactory.createMetaVar("M", inputs, baseType("o"));
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

  @Test
  public void testInequalityDifferentMetaVariables() {
    // M⟨x⟩
    Variable x = TermFactory.createBinder("x", baseType("o"));
    MetaVariable m1 = TermFactory.createMetaVar("M", arrowType("o", "o"), 1);
    MetaVariable m2 = TermFactory.createMetaVar("M", arrowType("o", "o"), 1);
    Term term1 = TermFactory.createMeta(m1, x);
    Term term2 = TermFactory.createMeta(m2, x);
    assertFalse(term1.equals(term2));
  }

  @Test
  public void testInequalityDifferentArguments() {
    // M⟨x⟩
    Variable x1 = TermFactory.createBinder("x", baseType("o"));
    Variable x2 = TermFactory.createBinder("x", baseType("o"));
    MetaVariable m = TermFactory.createMetaVar("M", arrowType("o", "o"), 1);
    Term term1 = TermFactory.createMeta(m, x1);
    Term term2 = TermFactory.createMeta(m, x2);
    assertFalse(term1.equals(term2));
  }

  @Test
  public void testSubstituteCorrectly() {
    // Z⟨g(x), c⟩ [x:=0, Z := λy,w.f(w, y)]
    Type type = arrowType(baseType("a"), arrowType(baseType("b"), arrowType("a", "b")));
    MetaVariable z = TermFactory.createMetaVar("Z", type, 2);
    Variable x = new Var("x", baseType("b"));
    Term arg1 = unaryTerm("g", baseType("a"), x);
    Term arg2 = constantTerm("c", baseType("b"));
    Term term = TermFactory.createMeta(z, arg1, arg2);

    Substitution gamma = new Subst();
    gamma.extend(x, constantTerm("0", baseType("b")));
    Variable y = new Binder("y", baseType("a"));
    Variable w = new Binder("w", baseType("b"));
    Term f = constantTerm("f",
      arrowType(baseType("b"), arrowType(baseType("a"), arrowType("a", "b"))));
    gamma.extend(z, TermFactory.createAbstraction(y, TermFactory.createAbstraction(w,
      TermFactory.createApp(f, w, y))));

    Term result = term.substitute(gamma);
    assertTrue(result.toString().equals("f(c, g(0))"));
  }

  @Test
  public void testDifficultSubstitution() {
    // Z⟨λx.a(x,y),F⟩
    Variable x = new Binder("x", baseType("A"));
    Variable y = new Binder("y", baseType("B"));
    Term a = constantTerm("a", arrowType(baseType("A"), arrowType("B", "A")));
    Term abs = new Abstraction(x, TermFactory.createApp(a, x, y));
    Variable f = new Binder("F", arrowType("A", "A"));
    MetaVariable z = TermFactory.createMetaVar("Z", arrowType(abs.queryType(),
      arrowType(f.queryType(), baseType("A"))), 2);
    Term term = TermFactory.createMeta(z, abs, f);
    // [x:=0, y:=1, F:=λz.h(z, x), Z := λF, G.F(G(0))]
    Substitution gamma = new Subst();
    gamma.extend(x, constantTerm("0", baseType("A")));
    gamma.extend(y, constantTerm("1", baseType("B")));
    Variable z2 = new Binder("z", baseType("A"));
    Term h = constantTerm("h", arrowType(baseType("A"), arrowType("A", "A")));
    Term abs1 = new Abstraction(z2, TermFactory.createApp(h, z2, x));
    gamma.extend(f, abs1);
    Variable g = new Binder("G", arrowType("A", "A"));
    Term zero = constantTerm("0", baseType("A"));
    Term abs2 = new Abstraction(f, new Abstraction(g, f.apply(g.apply(zero))));
    gamma.extend(z, abs2);
    // result of substituting: [λF, G.F(G(0))]⟨λx.a(x,1), λz.h(z, x)⟩⟩ = (λx.a(x,1))(λz.h(z, x)(0))
    // (note that it isn't normalised beyond that)
    assertTrue(term.substitute(gamma).toString().equals("(λx1.a(x1, 1))((λz.h(z, x))(0))"));
  }

  @Test
  public void testRenaming() {
    // Z⟨λx.a(x,y),F⟩ -- except all variables and meta-variables are called "v"
    Variable x = new Binder("x", baseType("A"));
    Variable f = new Binder("x", arrowType("A", "A"));
    Variable y = new Binder("x", baseType("B"));
    Term a = constantTerm("a", arrowType(baseType("A"), arrowType("B", "A")));
    Term abs = new Abstraction(x, TermFactory.createApp(a, x, y));
    MetaVariable z = TermFactory.createMetaVar("x", arrowType(abs.queryType(),
      arrowType(f.queryType(), baseType("A"))), 2);
    Term term = TermFactory.createMeta(z, abs, f);
    assertTrue(term.toString().equals("x__1⟨λx1.a(x1, x__3), x__2⟩"));
  }

  @Test
  public void testReplaceables() {
    // let's create: Z⟨Z⟨x,h(λz.c(z))⟩,g(y,x)⟩, where x and y are variables
    MetaVariable z = TermFactory.createMetaVar("Z", arrowType(baseType("a"),arrowType("b","a")), 2);
    FunctionSymbol g = new Constant("g", arrowType(baseType("b"),arrowType("a","b")));
    FunctionSymbol c = new Constant("c", arrowType("o", "o"));
    FunctionSymbol h = new Constant("h", arrowType(arrowType("o", "o"), baseType("b")));
    Variable x = new Binder("x", baseType("a"));
    Variable y = new Var("y", baseType("b"));
    Variable z2 = new Binder("z", baseType("o"));
    Term hlambdazcz = new Application(h, new Abstraction(z2, c.apply(z2)));
    Term t = TermFactory.createMeta(z, x, hlambdazcz);
    Term s = TermFactory.createMeta(z, t, new Application(g, y, x));
    ReplaceableList lst = s.freeReplaceables();
    assertTrue(lst.contains(x));
    assertTrue(lst.contains(y));
    assertTrue(lst.contains(z));

    Environment<Variable> env = s.vars();
    assertTrue(env.contains(x));
    assertTrue(env.contains(y));
    assertTrue(env.size() == 2);

    Environment<MetaVariable> menv = s.mvars();
    assertTrue(menv.contains(z));
    assertTrue(menv.size() == 2);
    assertTrue(t.mvars().size() == 1);
    assertTrue(hlambdazcz.mvars().size() == 0);
  }

  @Test
  public void testReplaceablesReuse() {
    // let's create: Z⟨g(x), Z⟨x,y⟩⟩
    Variable x = new Var("x", baseType("o"));
    Variable y = new Var("x", baseType("o"));
    Term gx = unaryTerm("g", baseType("o"), x);
    MetaVariable z =
      TermFactory.createMetaVar("Z", arrowType(baseType("o"), arrowType("o", "o")), 2);
    Term zxy = TermFactory.createMeta(z, x, y);
    Term term = TermFactory.createMeta(z, gx, zxy);
    assertTrue(gx.freeReplaceables() == x.freeReplaceables());
    assertTrue(zxy.freeReplaceables() == term.freeReplaceables());
    assertTrue(term.freeReplaceables().size() == 3);
  }

  @Test
  public void testBoundVars() {
    // let's create: F⟨λx.Z(x), Y, G⟨λz.z, λx,u.h(x,y)⟩⟩
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Variable z = new Binder("z", baseType("o"));
    Variable u = new Binder("u", baseType("o"));
    Variable bZ = new Var("Z", arrowType("o", "o"));
    Variable bY = new Var("Y", baseType("o"));
    FunctionSymbol h = new Constant("h", arrowType(baseType("o"), arrowType("o", "o")));
    MetaVariable g = TermFactory.createMetaVar("G", arrowType(arrowType("o", "o"),
      arrowType(arrowType(baseType("o"), arrowType("o", "o")), baseType("o"))), 2);
    MetaVariable f = TermFactory.createMetaVar("F",
      arrowType(arrowType("o", "o"), arrowType(baseType("o"), arrowType("o", "o"))), 3);
    Term ahxy = new Abstraction(x, new Abstraction(u, new Application(h, x, y)));
    Term az = new Abstraction(z, z);
    Term gterm = TermFactory.createMeta(g, az, ahxy);
    Term aZx = new Abstraction(x, new Application(bZ, x));
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(aZx);
    args.add(bY);
    args.add(gterm);
    Term fterm = new MetaApplication(f, args);

    ReplaceableList frees = fterm.freeReplaceables();
    ReplaceableList boundVars = fterm.boundVars();
    assertTrue(frees.size() == 5);
    assertTrue(boundVars.size() == 3);
    assertTrue(boundVars.contains(x));
    assertTrue(boundVars.contains(z));
    assertTrue(boundVars.contains(u));
    assertTrue(frees.contains(y));
    assertTrue(frees.contains(bY));
    assertTrue(frees.contains(bZ));
    assertTrue(frees.contains(f));
    assertTrue(frees.contains(g));
  }

  @Test
  public void testBoundVarsReuse() {
    // let's create: Z⟨λx.x, λx.x⟩
    Variable x = new Binder("x", baseType("o"));
    MetaVariable z = TermFactory.createMetaVar("Z", arrowType(arrowType("o", "o"),
      arrowType(arrowType("o", "o"), baseType("o"))), 2);
    Term abs1 = new Abstraction(x, x);
    Term abs2 = new Abstraction(x, x);
    Term term = TermFactory.createMeta(z, abs1, abs2);
    assertTrue(term.boundVars() == abs1.boundVars());
  }

  @Test
  public void testCorrectApplication() {
    Type o = baseType("o");
    Type a = baseType("a");
    Type type = arrowType(a, arrowType(o, a));
    MetaVariable x = TermFactory.createMetaVar("X", type, 1);
    Term c = constantTerm("c", arrowType(a, a));
    Term d = constantTerm("d", a);
    Term xc = TermFactory.createMeta(x, c.apply(d));
    Term xcb = xc.apply(constantTerm("b", o));
    assertTrue(xcb.toString().equals("X⟨c(d)⟩(b)"));
  }

  @Test
  public void testRefreshBinders() {
    // Z⟨λx.x, λx.x⟩
    Variable x = new Binder("x", baseType("o"));
    Term xx = new Abstraction(x, x);
    MetaVariable z = TermFactory.createMetaVar("Z", arrowType(arrowType("o", "o"),
      arrowType(arrowType("o", "o"), baseType("a"))), 2);
    Term term = TermFactory.createMeta(z, xx, xx);
    Term t = term.refreshBinders();
    assertTrue(t.equals(term));
    assertTrue(t.queryMetaVariable() == z);
    Variable x1 = t.queryMetaArgument(1).queryVariable();
    Variable x2 = t.queryMetaArgument(2).queryVariable();
    assertTrue(x1 != x2);
  }

  @Test
  public void testWellbehaved() {
    // Z⟨λx.x, x⟩
    Variable x = new Binder("x", baseType("a"));
    Term abs = new Abstraction(x, x);
    MetaVariable z = TermFactory.createMetaVar("Z", arrowType(arrowType("a", "a"),
      arrowType("a", "a")), 2);
    Term term = TermFactory.createMeta(z, abs, x);
    assertTrue(term.toString().equals("Z⟨λx1.x1, x⟩"));
    assertFalse(term.queryMetaArgument(1).queryVariable().equals(
                  term.queryMetaArgument(2).queryVariable()));
  }

  @Test
  public void testNullMatch() {
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    MetaVariable z =
      TermFactory.createMetaVar("Z", arrowType(baseType("o"), arrowType("o", "o")), 2);
    Term t = TermFactory.createMeta(z, x, y);
    Substitution subst = new Subst();
    assertThrows(NullPointerException.class, () -> t.match(null, subst));
  }

  @Test
  public void testNullSubst() {
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    MetaVariable z =
      TermFactory.createMetaVar("Z", arrowType(baseType("o"), arrowType("o", "o")), 2);
    Term t = TermFactory.createMeta(z, x, y);
    Substitution subst = new Subst();
    assertThrows(NullPointerException.class, () -> t.match(x, null));
  }

  private Term createTwoArgMeta(Term arg1, Term arg2) {
    Type type = arrowType(arg1.queryType(), arrowType(arg2.queryType(), baseType("o")));
    MetaVariable f = TermFactory.createMetaVar("F", type, 2);
    return TermFactory.createMeta(f, arg1, arg2);
  }

  @Test
  public void testNonPatternDueToNonVariableArg() {
    // F⟨a⟩ matched against a
    MetaVariable f = TermFactory.createMetaVar("F", arrowType("o", "o"), 1);
    Term a = constantTerm("a", baseType("o"));
    Term t = TermFactory.createMeta(f, a);
    Substitution subst = new Subst();
    assertThrows(PatternRequiredError.class, () -> t.match(a, subst));
  }

  @Test
  public void testNonPatternDueToVarArg() {
    // F⟨X⟩ matched against a
    Variable x = new Var("X", baseType("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType("o", "o"), 1);
    Term t = TermFactory.createMeta(f, x);
    Term a = constantTerm("a", baseType("o"));
    assertThrows(PatternRequiredError.class, () -> t.match(a, new Subst()));
  }

  @Test
  public void testNonPatternDueToSubstitutedVarArg() {
    // F⟨X⟩ matched against a, with X:=y
    Variable x = new Var("X", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType("o", "o"), 1);
    Term t = TermFactory.createMeta(f, x);
    Term a = constantTerm("a", baseType("o"));
    Substitution subst = new Subst();
    subst.extend(x, y);
    assertThrows(PatternRequiredError.class, () -> t.match(a, subst));
  }

  @Test
  public void testNonPatternDueToBinderNotSubstituted() {
    // F⟨x,y⟩ matched against a where x:=z, but y is not substituted
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Variable z = new Binder("Z", baseType("o"));
    Term t = createTwoArgMeta(x, y);
    Substitution subst = new Subst();
    subst.extend(x, z);
    assertThrows(PatternRequiredError.class, () ->
      t.match(constantTerm("a", baseType("o")), subst));
  }

  @Test
  public void testNonPatternDueToBinderArgSubstitutedToVar() {
    // F⟨x,y⟩ matched against a where x:=Z,y:=y
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Variable z = new Var("Z", baseType("o"));
    Term t = createTwoArgMeta(x, y);
    Substitution subst = new Subst();
    subst.extend(x, z);
    subst.extend(y, z);
    assertThrows(PatternRequiredError.class, () ->
      t.match(constantTerm("a", baseType("o")), subst));
  }

  @Test
  public void testNonPatternDueToDuplicateBinder() {
    // F⟨x,x⟩ matched against x
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Term t = createTwoArgMeta(x, x);
    assertThrows(PatternRequiredError.class, () -> t.match(x, new Subst()));
  }

  @Test
  public void testNonPatternDueToNonDistinctSubstitutedArgs() {
    // F⟨x,y⟩ matched against a where x:=z and y:=z
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Variable z = new Binder("z", baseType("o"));
    Term t = createTwoArgMeta(x, y);
    Substitution subst = new Subst();
    subst.extend(x, z);
    subst.extend(y, z);
    assertThrows(PatternRequiredError.class, () ->
      t.match(constantTerm("a", baseType("o")), subst));
  }

  @Test
  public void testProperMatching() {
    // F⟨x,y⟩ matched against h(y, x)
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Variable z = new Binder("z", baseType("o"));
    Term t = createTwoArgMeta(x, y);
    Substitution subst = new Subst();
    subst.extend(x, x);
    subst.extend(y, y);
    Term result =
      TermFactory.createApp(constantTerm("h", arrowType(baseType("o"), arrowType("o", "o"))), y, x);
    assertTrue(t.match(result, subst) == null);
    assertTrue(subst.get(x) == x);
    assertTrue(subst.get(y) == y);
    assertTrue(subst.get(t.queryMetaVariable()).toString().equals("λx.λy.h(y, x)"));
  }

  @Test
  public void testProperMatchingWithSwitchedVariables() {
    // F⟨x,y⟩ matched against h(y, x) where x:=y and y:=x
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Variable z = new Binder("z", baseType("o"));
    Term t = createTwoArgMeta(x, y);
    Substitution subst = new Subst();
    subst.extend(x, y);
    subst.extend(y, x);
    Term result =
      TermFactory.createApp(constantTerm("h", arrowType(baseType("o"), arrowType("o", "o"))), y, x);
    assertTrue(t.match(result, subst) == null);
    assertTrue(subst.get(t.queryMetaVariable()).toString().equals("λy.λx.h(y, x)"));
  }

  @Test
  public void testLateAssignmentToArgument() {
    // g(F⟨x⟩, x) against g(x, y)
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("x", baseType("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType("o", "o"), 1);
    Term g = constantTerm("g", arrowType(baseType("o"), arrowType("o", "o")));
    Term term = new Application(g, TermFactory.createMeta(f, x), x);

    Term m = new Application(g, x, y);
    Substitution subst = new Subst();
    assertTrue(term.match(m, subst) == null);
    assertTrue(subst.get(x) == y);
    assertTrue(subst.get(f).equals(new Abstraction(y, x)));
  }

  @Test
  public void testTooLateAssignmentToArgument() {
    // g(x, F⟨x⟩) against g(y, x)
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("x", baseType("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType("o", "o"), 1);
    Term g = constantTerm("g", arrowType(baseType("o"), arrowType("o", "o")));
    Term term = new Application(g, x, TermFactory.createMeta(f, x));

    Term m = new Application(g, y, x);
    Substitution subst = new Subst();
    assertThrows(PatternRequiredError.class, () -> term.match(m, subst));
  }

  @Test
  public void testMatchingFailsExistingMapping() {
    // F⟨x,y⟩ against g(x,y) where F is mapped to λxy.g(y,x)
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType(baseType("o"),arrowType("o","o")), 2);
    Term term = TermFactory.createMeta(f, x, y);
    Term g = constantTerm("g", arrowType(baseType("o"), arrowType("o", "o")));
    Term m = new Application(g, x, y);
    Substitution subst = new Subst();
    subst.extend(x, x);
    subst.extend(y, y);
    subst.extend(f, new Abstraction(x, new Abstraction(y, new Application(g, y, x))));
    assertTrue(term.match(m, subst).equals(
      "Meta-variable F is mapped to both λx.λy.g(y, x) and to λx.λy.g(x, y)."));
  }

  @Test
  public void testMatchingCorrespondsExactlyToExistingMapping() {
    // F⟨x,y⟩ against g(x,y) where F is mapped to λxy.g(x,y)
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType(baseType("o"),arrowType("o","o")), 2);
    Term term = TermFactory.createMeta(f, x, y);
    Term g = constantTerm("g", arrowType(baseType("o"), arrowType("o", "o")));
    Term m = new Application(g, x, y);
    Substitution subst = new Subst();
    subst.extend(x, x);
    subst.extend(y, y);
    subst.extend(f, new Abstraction(x, new Abstraction(y, new Application(g, x, y))));
    assertTrue(term.match(m, subst) == null);
  }

  @Test
  public void testMatchingAlphaCorrespondsToExistingMapping() {
  // F⟨x,y⟩ against g(u,h(v)) where x:=v,y:=u,F:=λab.g(b,h(a))
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Variable u = new Binder("u", baseType("o"));
    Variable v = new Binder("v", baseType("o"));
    Variable a = new Binder("a", baseType("o"));
    Variable b = new Binder("b", baseType("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType(baseType("o"),arrowType("o","o")), 2);
    Term term = TermFactory.createMeta(f, x, y);
    Term g = constantTerm("g", arrowType(baseType("o"), arrowType("o", "o")));
    Term h = constantTerm("h", arrowType("o", "o"));
    Term m = new Application(g, u, h.apply(v));
    Substitution subst = new Subst();
    subst.extend(x, v);
    subst.extend(y, u);
    subst.extend(f, new Abstraction(a, new Abstraction(b, new Application(g, b, h.apply(a)))));
    assertTrue(term.match(m, subst) == null);
  }

  @Test
  public void testNonLinearMetaOccurrence() {
    // λx.λy.g(F⟨x⟩, F⟨y⟩) against λa.λb.g(h(z,a), h(z,b))
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Variable z = new Binder("z", baseType("o"));
    Variable a = new Binder("a", baseType("o"));
    Variable b = new Binder("b", baseType("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType("o", "o"), 1);
    Term g = constantTerm("g", arrowType(baseType("o"), arrowType("o", "o")));
    Term h = constantTerm("h", arrowType(baseType("o"), arrowType("o", "o")));
    Term term = new Abstraction(x, new Abstraction(y, new Application(g, TermFactory.createMeta(f, x),
      TermFactory.createMeta(f, y))));
    Term m = new Abstraction(a, new Abstraction(b, new Application(g, new Application(h, z, a),
      new Application(h, z, b))));
    Substitution subst = term.match(m);
    assertTrue(subst.get(f).equals(new Abstraction(x, new Application(h, z, x))));
  }

  @Test
  public void testNonMatchDueToNonLinearity() {
    // λx.g(F⟨x⟩, F⟨x⟩) against λy.g(h(z,y), h(y,z))
    Variable x = new Binder("x", baseType("o"));
    Variable y = new Binder("y", baseType("o"));
    Variable z = new Binder("z", baseType("o"));
    MetaVariable f = TermFactory.createMetaVar("F", arrowType("o", "o"), 1);
    Term g = constantTerm("g", arrowType(baseType("o"), arrowType("o", "o")));
    Term h = constantTerm("h", arrowType(baseType("o"), arrowType("o", "o")));
    Term fx = TermFactory.createMeta(f, x);
    Term term = new Abstraction(x, new Application(g, fx, fx));
    Term m = new Abstraction(y, new Application(g, new Application(h,z,y), new Application(h,y,z)));
    assertTrue(term.match(m, new Subst()) != null);
  }
}

