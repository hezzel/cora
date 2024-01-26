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

package cora.rewriting;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.exceptions.IllegalRuleError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.TypingError;
import cora.types.Type;
import cora.types.TypeFactory;
import cora.terms.*;
import cora.reader.CoraInputReader;

public class RuleTest {
  private Type type(String txt) {
    try { return CoraInputReader.readType(txt); }
    catch (Exception e) { System.out.println(e); return null; }
  }

  private FunctionSymbol makeConstant(String name, String ty) {
    return TermFactory.createConstant(name, type(ty));
  }

  @Test(expected = NullInitialisationError.class)
  public void testLeftNullCreation() {
    Rule rule = RuleFactory.createRule(makeConstant("a", "b"), null);
  }

  @Test(expected = NullInitialisationError.class)
  public void testRightNullCreation() {
    Rule rule = RuleFactory.createApplicativeRule(null, makeConstant("a", "b"));
  }

  @Test(expected = TypingError.class)
  public void testIlltypedRule() {
    Variable x = TermFactory.createVar("x", type("a"));
    Term left = makeConstant("id", "a → b → a").apply(x); // id(x)
    Rule rule = RuleFactory.createRule(left, x);
  }

  @Test(expected = IllegalRuleError.class)
  public void testIllegalFreshVariableOnTheRight() {
    // f(λx.x, y) → g(y, z)
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createVar("y", type("o"));
    Variable z = TermFactory.createVar("z", type("o"));
    Term f = TermFactory.createConstant("f", type("(o → o) → o → o"));
    Term g = TermFactory.createConstant("g", type("o → o → o"));
    Term left = TermFactory.createApp(f, TermFactory.createAbstraction(x, x), y);
    Term right = TermFactory.createApp(g, y, z);
    Rule rule = RuleFactory.createRule(left, right);
  }

  @Test
  public void testLegalFreshVariableOnTheRight() {
    // f(λx.x, y) → g(y, z)
    Variable x = TermFactory.createBinder("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Variable z = TermFactory.createVar("z", type("Int"));
    Term f = TermFactory.createConstant("f", type("(Int → Int) → Int → Int"));
    Term g = TermFactory.createConstant("g", type("Int → Int → Int"));
    Term left = TermFactory.createApp(f, TermFactory.createAbstraction(x, x), y);
    Term right = TermFactory.createApp(g, y, z);
    Rule rule = RuleFactory.createRule(left, right);
    assertTrue(rule.rightHasFreshVariables());
  }

  @Test(expected = IllegalRuleError.class)
  public void testRuleNotClosed() {
    // f(x, y) → y with x a binder
    Variable x = TermFactory.createBinder("x", type("a"));
    Variable y = TermFactory.createVar("y", type("b"));
    Term f = TermFactory.createConstant("f", type("a → b → b"));
    Term left = TermFactory.createApp(f, x, y);
    Rule rule = RuleFactory.createRule(left, y);
  }

  @Test(expected = IllegalRuleError.class)
  public void testApplicativeRuleNotApplicative() {
    // a → g(λz.z)
    Term a = makeConstant("a", "o");
    Term g = makeConstant("g", "(a → a) → o");
    Variable z = TermFactory.createBinder("z", type("a"));
    Rule rule = RuleFactory.createApplicativeRule(a, g.apply(TermFactory.createAbstraction(z, z)));
  }

  @Test(expected = IllegalRuleError.class)
  public void testCMSRuleWithMetaVariables() {
    // f(λx.Z⟨x⟩) → a
    Term f = TermFactory.createConstant("f", type("(o → o) → o"));
    Variable x = TermFactory.createBinder("x", type("o"));
    MetaVariable z = TermFactory.createMetaVar("Z", type("o → o"), 1);
    Term left = f.apply(TermFactory.createAbstraction(x, TermFactory.createMeta(z, x)));
    Term right = makeConstant("a", "o");
    Rule rule = RuleFactory.createCFSRule(left, right);
  }

  @Test(expected = IllegalRuleError.class)
  public void testNonPatternRule() {
    // f(λx.Z(x)) → a
    Term f = TermFactory.createConstant("f", type("(o → o) → o"));
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable z = TermFactory.createVar("Z", type("o → o"));
    Term left = f.apply(TermFactory.createAbstraction(x, z.apply(x)));
    Term right = makeConstant("a", "o");
    Rule rule = RuleFactory.createPatternRule(left, right);
  }

  @Test(expected = IllegalRuleError.class)
  public void testConstraintNotBool() {
    // f(x) → x | x
    Term f = TermFactory.createConstant("f", type("Int → Int"));
    Variable x = TermFactory.createVar("x", type("Int"));
    Rule rule = RuleFactory.createApplicativeRule(f.apply(x), x, x);
  }

  @Test(expected = IllegalRuleError.class)
  public void testConstraintNotTheory() {
    // f(x) → x | x > a
    Term a = TermFactory.createConstant("a", type("Int"));
    Term f = TermFactory.createConstant("f", type("Int → Int"));
    Variable x = TermFactory.createVar("x", type("Int"));
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(a);
    Rule rule = RuleFactory.createFirstOrderRule(f.apply(x), x, constraint);
  }

  @Test(expected = IllegalRuleError.class)
  public void testConstraintWithNonTheoryVariable() {
    // f(x) → x | x > 1 where x has type Int, but it is not marked as a theory sort
    Term f = TermFactory.createConstant("f", type("Int → Int"));
    Variable x = TermFactory.createVar("x", TypeFactory.createSort("Int"));
    Term one = TheoryFactory.createValue(1);
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(one);
    Rule rule = RuleFactory.createRule(f.apply(x), x, constraint);
  }

  @Test(expected = IllegalRuleError.class)
  public void testConstraintWithBinder() {
    // f(x) → x | x > 1 where x is a binder
    Term f = TermFactory.createConstant("f", type("Int → Int"));
    Variable x = TermFactory.createBinder("x", type("Int"));
    Term one = TheoryFactory.createValue(1);
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(one);
    Rule rule = RuleFactory.createRule(f.apply(x), x, constraint);
  }

  @Test(expected = IllegalRuleError.class)
  public void testConstraintWithLambda() {
    // f(x) → x | x > (λy.y)(1)
    Term f = TermFactory.createConstant("f", type("Int → Int"));
    Variable x = TermFactory.createVar("x", type("Int"));
    Term one = TheoryFactory.createValue(1);
    Variable y = TermFactory.createBinder("y", type("Int"));
    Term abs = TermFactory.createAbstraction(y, y);
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(abs.apply(one));
    Rule rule = RuleFactory.createRule(f.apply(x), x, constraint);
  }

  @Test
  public void testConstraintWithFreshVariable() {
    // f(x) → x | x > y
    Term f = TermFactory.createConstant("f", type("Int → Int"));
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(y);
    Rule rule = RuleFactory.createApplicativeRule(f.apply(x), x, constraint);
    assertTrue(rule.toString().equals("f(x) → x | x > y"));
    assertFalse(rule.rightHasFreshVariables());
  }

  @Test
  public void testConstraintWithFreshVariableAlsoInRight() {
    // f(x) → y | x > y
    Term f = TermFactory.createConstant("f", type("Int → Int"));
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(y);
    Rule rule = RuleFactory.createApplicativeRule(f.apply(x), y, constraint);
    assertTrue(rule.toString().equals("f(x) → y | x > y"));
    assertTrue(rule.rightHasFreshVariables());
  }

  @Test
  public void testVariableNaming() {
    // f(x, y) → g(y, λz.z) -- except all variables have the same default name
    Variable x = TermFactory.createVar("x", type("a"));
    Variable y = TermFactory.createVar("x", type("b"));
    Variable z = TermFactory.createBinder("x", type("c"));
    FunctionSymbol f = makeConstant("f", "a → b → d");
    FunctionSymbol g = makeConstant("g", "b → (c → c) → d");
    Term left = TermFactory.createApp(f, x, y);
    Term right = TermFactory.createApp(g, y, TermFactory.createAbstraction(z, z));
    Rule rule = RuleFactory.createCFSRule(left, right);
    assertTrue(rule.toString().equals("f(x__1, x__2) → g(x__2, λx1.x1)"));
  }

  @Test
  public void testBasics() {
    // f(λx.x(a), y) → y
    Variable x = TermFactory.createBinder("x", type("o → o"));
    Term a = makeConstant("a", "o");
    Term abs = TermFactory.createAbstraction(x, x.apply(a));
    Variable y = TermFactory.createVar("y", type("u"));
    Term f = makeConstant("f", "((o → o) → o) → u → u");
    Term left = TermFactory.createApp(f, abs, y);
    Rule rule = RuleFactory.createPatternRule(left, y);
    assertTrue(rule.queryLeftSide().equals(left));
    assertTrue(rule.queryRightSide().equals(y));
    assertTrue(rule.queryType().equals(type("u")));
    assertTrue(rule.toString().equals("f(λx.x(a), y) → y"));
    assertFalse(rule.isApplicative());
    assertTrue(rule.isPatternRule());

    rule = RuleFactory.createRule(y, y);
    assertTrue(rule.toString().equals("y → y"));
    assertTrue(rule.isApplicative());
    assertFalse(rule.isPatternRule());
  }

  @Test
  public void testSuccessfulUnconstrainedRootApplication() {
    // rule: f(g(x), λz.y(z)) → h(x, y(3)), λz.z) :: Int → Int
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int → Bool"));
    Variable z = TermFactory.createBinder("z", type("Int"));
    Term three = makeConstant("3", "Int");
    Term f = makeConstant("f", "Bool → (Int → Bool) → Int → Int");
    Term g = makeConstant("g", "Int → Bool");
    Term h = makeConstant("h", "Int → Bool → (Int → Int) → Int → Int");
    Term left = TermFactory.createApp(f, g.apply(x), TermFactory.createAbstraction(z, y.apply(z)));
    Term right = TermFactory.createApp(h, x, y.apply(three)).apply(
      TermFactory.createAbstraction(z, z));
    Rule rule = RuleFactory.createRule(left, right);

    // instance: f(g(j(5, z)), λa.(λb,c.true)(3, a))
    Term top = makeConstant("true", "Bool");
    Term five = makeConstant("5", "Int");
    Term j = makeConstant("j", "Int → Int → Int");
    Term gterm = g.apply(TermFactory.createApp(j, five, z));
    Variable a = TermFactory.createBinder("a", type("Int"));
    Variable b = TermFactory.createBinder("b", type("Int"));
    Variable c = TermFactory.createBinder("c", type("Int"));
    Term abs1 = TermFactory.createAbstraction(b, TermFactory.createAbstraction(c, top));
    Term abs2 = TermFactory.createAbstraction(a, TermFactory.createApp(abs1, three, a));

    Term instance = TermFactory.createApp(f, gterm, abs2);
    assertTrue(rule.applicable(instance));
    assertTrue(rule.apply(instance).toString().equals("h(j(5, z), (λb.λc.true)(3, 3), λz1.z1)"));
  }

  @Test
  public void testSuccessfulConstrainedRootApplication() {
    // rule: f(H, x) → H(g(y), z) | 0 < y ∧ y < x
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Variable z = TermFactory.createVar("z", type("Int"));
    Variable h = TermFactory.createVar("H", type("o → Int → Int"));
    Term f = makeConstant("f", "(o → Int → Int) → Int → Int");
    Term g = makeConstant("g", "Int → o");
    Term left = TermFactory.createApp(f, h, x);
    Term right = TermFactory.createApp(h, g.apply(y), z);
    Term constr = TermFactory.createApp(TheoryFactory.andSymbol,
      TermFactory.createApp(TheoryFactory.smallerSymbol, TheoryFactory.createValue(0), y),
      TermFactory.createApp(TheoryFactory.smallerSymbol, y, x));
    Rule rule = RuleFactory.createApplicativeRule(left, right, constr);

    // instance: f(q(false), 3)
    Term qq = makeConstant("q", "(Bool → o → Int → Int)").apply(TheoryFactory.createValue(false));
    Term instance = TermFactory.createApp(f, qq, TheoryFactory.createValue(3));

    assertTrue(rule.applicable(instance));
    assertTrue(rule.apply(instance) != null);
    //System.out.println(rule.apply(instance).toString());
  }

  @Test
  public void testFailedRootApplication() {
    Variable x = TermFactory.createVar("x", type("Int"));
    FunctionSymbol f = makeConstant("f", "Int → Int → Int");
    Rule rule = RuleFactory.createApplicativeRule(TermFactory.createApp(f, x, x), x);
    // rule: f(x, x) -> x
    Term noninstance = TermFactory.createApp(f, makeConstant("1", "Int"), makeConstant("2", "Int"));
    // noninstance: f(1, 2)

    assertFalse(rule.applicable(noninstance));
    assertTrue(rule.apply(noninstance) == null);
  }

  @Test
  public void testFailedSatisfiabilityCheck() {
    // rule: f(x) → x | 0 < y ∧ y < x
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Term f = makeConstant("f", "Int → Int");
    Term constr = TermFactory.createApp(TheoryFactory.andSymbol,
      TermFactory.createApp(TheoryFactory.smallerSymbol, TheoryFactory.createValue(0), y),
      TermFactory.createApp(TheoryFactory.smallerSymbol, y, x));
    Rule rule = RuleFactory.createApplicativeRule(f.apply(x), x, constr);

    // instance: f(1)
    Term instance = f.apply(TheoryFactory.createValue(1));
    assertFalse(rule.applicable(instance));
    assertTrue(rule.apply(instance) == null);
  }

  @Test
  public void testSuccessfulHeadApplication() {
    // rule: f(x, x) → g(x(u)) | u = -3
    Variable x = TermFactory.createVar("x", type("Int → Int"));
    Variable u = TermFactory.createVar("x", type("Int"));
    Term f = makeConstant("f", "(Int → Int) → (Int → Int) → Bool → Int → a");
    Term g = makeConstant("g", "Int → Bool → Int → a");
    Term left = TermFactory.createApp(f, x, x);
    Term right = TermFactory.createApp(g, x.apply(u));
    Term constr = TermFactory.createApp(
      TheoryFactory.equalSymbol, u, TheoryFactory.createValue(-3));
    Rule rule = RuleFactory.createRule(left, right, constr);

    // instance: f(λy.h(y), λz.h(z), true, 7)
    Variable y = TermFactory.createBinder("y", type("Int"));
    Variable z = TermFactory.createBinder("z", type("Int"));
    Term h = makeConstant("h", "Int → Int");
    Term top = makeConstant("true", "Bool");
    Term seven = makeConstant("7", "Int");
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(TermFactory.createAbstraction(y, h.apply(y)));
    args.add(TermFactory.createAbstraction(z, h.apply(z)));
    args.add(top);
    args.add(seven);
    Term instance = f.apply(args);

    // target: g((λy.h(y))(-3), true, 7)
    ArrayList<Term> targs = new ArrayList<Term>();
    targs.add(args.get(0).apply(TheoryFactory.createValue(-3)));
    targs.add(top);
    targs.add(seven);
    Term target = g.apply(targs);

    assertTrue(rule.applicable(instance));
    assertTrue(rule.apply(instance).equals(target));
  }

  @Test
  public void testFailedHeadApplication() {
    Variable x = TermFactory.createVar("x", type("Int → Int"));
    FunctionSymbol f = makeConstant("f", "(Int → Int) → (Int → Int)");
    FunctionSymbol g = makeConstant("g", "Int → Int");
  
    Rule rule = RuleFactory.createRule(f.apply(x), x);
    // rule: f(x) -> x : Int -> Int
  
    Term noninstance = g.apply(makeConstant("0", "Int"));
    // noninstance: g 0 : Int
  
    assertFalse(rule.applicable(noninstance));
    assertTrue(rule.apply(noninstance) == null);
  }

  @Test
  public void testWrongTypeApplication() {
    Variable x = TermFactory.createVar("x", type("Bool → Int"));
    FunctionSymbol f = makeConstant("f", "(Bool → Int) → Bool → Int");
    FunctionSymbol g = makeConstant("f", "(Bool → Int) → Int → Int");
  
    Rule rule = RuleFactory.createRule(f.apply(x), x);
    // rule: f(x) -> x : Bool -> Int
  
    Term noninstance = TermFactory.createApp(g, x, makeConstant("0", "Int"));
    // noninstance: g(x,0) : Int
  
    assertFalse(rule.applicable(noninstance));
    assertTrue(rule.apply(noninstance) == null);
  }

  @Test
  public void testConstraintNotSatisfied() {
    // sum(x) → 0 [x ≤ 0] applied to sum(3)
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    FunctionSymbol sum = makeConstant("sum", "Int → Int");
    Term zero = TheoryFactory.createValue(0);
    Term constraint = TheoryFactory.leqSymbol.apply(x).apply(zero);
    Rule rule = RuleFactory.createRule(sum.apply(x), zero, constraint);
    Term term = sum.apply(TheoryFactory.createValue(3));
    assertFalse(rule.applicable(term));
    assertTrue(rule.apply(term) == null);
  }

  @Test
  public void testConstraintVariableNotInstantiatedWithValue() {
    // sum(x) → x + sum(x-1) [x > 0] applied to sum(2 + 1)
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term nul = TheoryFactory.createValue(0);
    Term one = TheoryFactory.createValue(1);
    Term two = TheoryFactory.createValue(2);
    Term neg = TheoryFactory.createValue(-1);
    FunctionSymbol sum = makeConstant("sum", "Int → Int");
    Term left = sum.apply(x);
    Term right = TheoryFactory.plusSymbol.apply(x).apply(
      sum.apply(TheoryFactory.plusSymbol.apply(x).apply(neg)));
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(nul);
    Rule rule = RuleFactory.createFirstOrderRule(left, right, constraint);

    Term addition = TheoryFactory.plusSymbol.apply(two).apply(one);
    Term term = sum.apply(addition);
    assertFalse(rule.applicable(term));
    assertTrue(rule.apply(term) == null);
  }

  @Test
  public void testConstraintApplicable() {
    // sum(x) → x + sum(x-1) | x > 0 applied to sum(5)
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term nul = TheoryFactory.createValue(0);
    Term one = TheoryFactory.createValue(1);
    Term neg = TheoryFactory.createValue(-1);
    FunctionSymbol sum = makeConstant("sum", "Int → Int");
    Term left = sum.apply(x);
    Term right = TheoryFactory.plusSymbol.apply(x).apply(
      sum.apply(TheoryFactory.plusSymbol.apply(x).apply(neg)));
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(nul);
    Rule rule = RuleFactory.createFirstOrderRule(left, right, constraint);

    Term term = sum.apply(TheoryFactory.createValue(5));
    assertTrue(rule.applicable(term));
    assertTrue(rule.apply(term).toString().equals("5 + sum(5 - 1)"));
  }

  @Test(expected = IllegalRuleError.class)
  public void testLhsTheory() {
    // x + 0 → x
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term lhs = TheoryFactory.plusSymbol.apply(x).apply(TheoryFactory.createValue(0));
    RuleFactory.createFirstOrderRule(lhs, x, null);
  }
}

