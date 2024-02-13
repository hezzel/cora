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
}

