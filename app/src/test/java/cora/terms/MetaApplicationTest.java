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

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import charlie.exceptions.*;
import cora.utils.Pair;
import cora.types.Type;
import cora.types.TypeFactory;
import cora.terms.position.*;

import static org.junit.jupiter.api.Assertions.*;

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
    assertThrows(ArityError.class, () -> TermFactory.createMeta(z, s, s));
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(constantTerm("a", baseType("a")));
    args.add(constantTerm("a", baseType("a")));
    args.add(constantTerm("a", baseType("a")));
    args.add(constantTerm("a", baseType("a")));
    assertThrows(ArityError.class, () -> TermFactory.createMeta(z, args));
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
}

