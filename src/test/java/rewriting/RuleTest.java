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
import cora.terms.*;
import cora.parsers.CoraInputReader;

public class RuleTest {
  private Type type(String txt) {
    try { return CoraInputReader.readTypeFromString(txt); }
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
    Term left = makeConstant("id", "a ⇒ b ⇒ a").apply(x); // id(x)
    Rule rule = RuleFactory.createRule(left, x);
  }

  @Test(expected = IllegalRuleError.class)
  public void testFreshVariableOnTheRight() {
    // f(λx.x, y) → g(y, z)
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createVar("y", type("o"));
    Variable z = TermFactory.createVar("z", type("o"));
    Term f = TermFactory.createConstant("f", type("(o ⇒ o) ⇒ o ⇒ o"));
    Term g = TermFactory.createConstant("g", type("o ⇒ o ⇒ o"));
    Term left = TermFactory.createApp(f, TermFactory.createAbstraction(x, x), y);
    Term right = TermFactory.createApp(g, y, z);
    Rule rule = RuleFactory.createRule(left, right);
  }

  @Test(expected = IllegalRuleError.class)
  public void testRuleNotClosed() {
    // f(x, y) → y with x a binder
    Variable x = TermFactory.createBinder("x", type("a"));
    Variable y = TermFactory.createVar("y", type("b"));
    Term f = TermFactory.createConstant("f", type("a ⇒ b ⇒ b"));
    Term left = TermFactory.createApp(f, x, y);
    Rule rule = RuleFactory.createRule(left, y);
  }

  @Test(expected = IllegalRuleError.class)
  public void testApplicativeRuleNotApplicative() {
    // a → g(λz.z)
    Term a = makeConstant("a", "o");
    Term g = makeConstant("g", "(a ⇒ a) ⇒ o");
    Variable z = TermFactory.createBinder("z", type("a"));
    Rule rule = RuleFactory.createApplicativeRule(a, g.apply(TermFactory.createAbstraction(z, z)));
  }

  @Test
  public void testVariableNaming() {
    // f(x, y) → g(y, λz.z) -- except all variables have the same default name
    Variable x = TermFactory.createVar("x", type("a"));
    Variable y = TermFactory.createVar("x", type("b"));
    Variable z = TermFactory.createBinder("x", type("c"));
    FunctionSymbol f = makeConstant("f", "a ⇒ b ⇒ d");
    FunctionSymbol g = makeConstant("g", "b ⇒ (c ⇒ c) ⇒ d");
    Term left = TermFactory.createApp(f, x, y);
    Term right = TermFactory.createApp(g, y, TermFactory.createAbstraction(z, z));
    Rule rule = RuleFactory.createRule(left, right);
    assertTrue(rule.toString().equals("f(x__1, x__2) → g(x__2, λx1.x1)"));
  }

  @Test
  public void testBasics() {
    // f(λx.x(a), y) → y
    Variable x = TermFactory.createBinder("x", type("o ⇒ o"));
    Term a = makeConstant("a", "o");
    Term abs = TermFactory.createAbstraction(x, x.apply(a));
    Variable y = TermFactory.createVar("y", type("u"));
    Term f = makeConstant("f", "((o ⇒ o) ⇒ o) ⇒ u ⇒ u");
    Term left = TermFactory.createApp(f, abs, y);
    Rule rule = RuleFactory.createRule(left, y);
    assertTrue(rule.queryLeftSide().equals(left));
    assertTrue(rule.queryRightSide().equals(y));
    assertTrue(rule.queryType().equals(type("u")));
    assertTrue(rule.toString().equals("f(λx.x(a), y) → y"));
    assertFalse(rule.isApplicative());

    rule = RuleFactory.createRule(y, y);
    assertTrue(rule.toString().equals("y → y"));
    assertTrue(rule.isApplicative());
  }

  @Test
  public void testSuccessfulRootApplication() {
    // rule: f(g(x), λz.y(z)) → h(x, y(3)), λz.z) :: Int ⇒ Int
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int ⇒ Bool"));
    Variable z = TermFactory.createBinder("z", type("Int"));
    Term three = makeConstant("3", "Int");
    Term f = makeConstant("f", "Bool ⇒ (Int ⇒ Bool) ⇒ Int ⇒ Int");
    Term g = makeConstant("g", "Int ⇒ Bool");
    Term h = makeConstant("h", "Int ⇒ Bool ⇒ (Int ⇒ Int) ⇒ Int ⇒ Int");
    Term left = TermFactory.createApp(f, g.apply(x), TermFactory.createAbstraction(z, y.apply(z)));
    Term right = TermFactory.createApp(h, x, y.apply(three)).apply(
      TermFactory.createAbstraction(z, z));
    Rule rule = RuleFactory.createRule(left, right);

    // instance: f(g(j(5, z)), λa.(λb,c.true)(3, a))
    Term top = makeConstant("true", "Bool");
    Term five = makeConstant("5", "Int");
    Term j = makeConstant("j", "Int ⇒ Int ⇒ Int");
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
  public void testFailedRootApplication() {
    Variable x = TermFactory.createVar("x", type("Int"));
    FunctionSymbol f = makeConstant("f", "Int ⇒ Int ⇒ Int");
    Rule rule = RuleFactory.createApplicativeRule(TermFactory.createApp(f, x, x), x);
    // rule: f(x, x) -> x
    Term noninstance = TermFactory.createApp(f, makeConstant("1", "Int"), makeConstant("2", "Int"));
    // noninstance: f(1, 2)

    assertFalse(rule.applicable(noninstance));
    assertTrue(rule.apply(noninstance) == null);
  }

  @Test
  public void testSuccessfulHeadApplication() {
    // rule: f(x, x) → g(x(0))
    Variable x = TermFactory.createVar("x", type("Int ⇒ Int"));
    Term f = makeConstant("f", "(Int ⇒ Int) ⇒ (Int ⇒ Int) ⇒ Bool ⇒ Int ⇒ a");
    Term g = makeConstant("g", "Int ⇒ Bool ⇒ Int ⇒ a");
    Term zero = makeConstant("0", "Int");
    Term left = TermFactory.createApp(f, x, x);
    Term right = TermFactory.createApp(g, x.apply(zero));
    Rule rule = RuleFactory.createRule(left, right);

    // instance: f(λy.h(y), λz.h(z), true, 7)
    Variable y = TermFactory.createBinder("y", type("Int"));
    Variable z = TermFactory.createBinder("z", type("Int"));
    Term h = makeConstant("h", "Int ⇒ Int");
    Term top = makeConstant("true", "Bool");
    Term seven = makeConstant("7", "Int");
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(TermFactory.createAbstraction(y, h.apply(y)));
    args.add(TermFactory.createAbstraction(z, h.apply(z)));
    args.add(top);
    args.add(seven);
    Term instance = f.apply(args);

    // target: g((λy.h(y))(0), true, 7)
    ArrayList<Term> targs = new ArrayList<Term>();
    targs.add(args.get(0).apply(zero));
    targs.add(top);
    targs.add(seven);
    Term target = g.apply(targs);

    assertTrue(rule.applicable(instance));
    assertTrue(rule.apply(instance).equals(target));
  }

  @Test
  public void testFailedHeadApplication() {
    Variable x = TermFactory.createVar("x", type("Int ⇒ Int"));
    FunctionSymbol f = makeConstant("f", "(Int ⇒ Int) ⇒ (Int ⇒ Int)");
    FunctionSymbol g = makeConstant("g", "Int ⇒ Int");
  
    Rule rule = RuleFactory.createRule(f.apply(x), x);
    // rule: f(x) -> x : Int -> Int
  
    Term noninstance = g.apply(makeConstant("0", "Int"));
    // noninstance: g 0 : Int
  
    assertFalse(rule.applicable(noninstance));
    assertTrue(rule.apply(noninstance) == null);
  }

  @Test
  public void testWrongTypeApplication() {
    Variable x = TermFactory.createVar("x", type("Bool ⇒ Int"));
    FunctionSymbol f = makeConstant("f", "(Bool ⇒ Int) ⇒ Bool ⇒ Int");
    FunctionSymbol g = makeConstant("f", "(Bool ⇒ Int) ⇒ Int ⇒ Int");
  
    Rule rule = RuleFactory.createRule(f.apply(x), x);
    // rule: f(x) -> x : Bool -> Int
  
    Term noninstance = TermFactory.createApp(g, x, makeConstant("0", "Int"));
    // noninstance: g(x,0) : Int
  
    assertFalse(rule.applicable(noninstance));
    assertTrue(rule.apply(noninstance) == null);
  }
}

