/**************************************************************************************************
 Copyright 2024--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.trs;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.Set;

import charlie.util.NullStorageException;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.parser.CoraParser;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.*;
import charlie.trs.TrsProperties.*;

public class RuleTest {
  private Type type(String txt) {
    try { return CoraParser.readType(txt); }
    catch (Exception e) { System.out.println(e); return null; }
  }

  private FunctionSymbol makeConstant(String name, String ty) {
    return TermFactory.createConstant(name, type(ty));
  }

  @Test
  public void testNullCreation() {
    Term a = makeConstant("a", "b");
    assertThrows(NullStorageException.class, () -> new Rule(a, null));
    assertThrows(NullStorageException.class, () -> new Rule(null, a));
    assertThrows(NullStorageException.class, () -> new Rule(a, a, null));
  }

  @Test
  public void testIlltypedRule() {
    Variable x = TermFactory.createVar("x", type("a"));
    Term left = makeConstant("id", "a → b → a").apply(x); // id(x)
    assertThrows(TypingException.class, () -> new Rule(left, x));
  }

  @Test
  public void testFreshVariableOnTheRight() {
    // f(λx.x, y) → g(y, z)
    Variable x = TermFactory.createBinder("x", type("o"));
    Variable y = TermFactory.createVar("y", type("o"));
    Variable z = TermFactory.createVar("z", type("o"));
    Term f = TermFactory.createConstant("f", type("(o → o) → o → o"));
    Term g = TermFactory.createConstant("g", type("o → o → o"));
    Term left = TermFactory.createApp(f, TermFactory.createAbstraction(x, x), y);
    Term right = TermFactory.createApp(g, y, z);
    Rule rule = new Rule(left, right);
    assertTrue(rule.queryProperties().rightReplaceablePolicy() == FreshRight.ANY);
  }

  @Test
  public void testFreshVariableOnTheRightAndInConstraint() {
    // f(λx.x, y) → g(y, z) | z = z
    Variable x = TermFactory.createBinder("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Variable z = TermFactory.createVar("z", type("Int"));
    Term f = TermFactory.createConstant("f", type("(Int → Int) → Int → Int"));
    Term g = TermFactory.createConstant("g", type("Int → Int → Int"));
    Term left = TermFactory.createApp(f, TermFactory.createAbstraction(x, x), y);
    Term right = TermFactory.createApp(g, y, z);
    Term constraint = TheoryFactory.createEquality(z, z);
    Rule rule = new Rule(left, right, constraint);
    assertTrue(rule.queryLVars().size() == 1);
    assertTrue(rule.queryLVars().contains(z));
  }

  @Test
  public void testRuleNotClosed() {
    // f(x, y) → y with x a binder
    Variable x = TermFactory.createBinder("x", type("a"));
    Variable y = TermFactory.createVar("y", type("b"));
    Term f = TermFactory.createConstant("f", type("a → b → b"));
    Term left = TermFactory.createApp(f, x, y);
    assertThrows(IllegalRuleException.class, () -> new Rule(left, y));
  }

  @Test
  public void testPropertiesOne() {
    // a → g(λz.z)
    Term a = makeConstant("a", "o");
    Term g = makeConstant("g", "(a → a) → o");
    Variable z = TermFactory.createBinder("z", type("a"));
    Rule rule = new Rule(a, g.apply(TermFactory.createAbstraction(z, z)));
    RuleRestrictions properties = rule.queryProperties();
    assertTrue(properties.queryLevel() == Level.LAMBDA);
    assertFalse(properties.theoriesUsed());
    assertFalse(properties.productsUsed());
    assertTrue(properties.patternStatus() == Lhs.PATTERN);
    assertTrue(properties.rootStatus() == Root.FUNCTION);
    assertTrue(properties.rightReplaceablePolicy() == FreshRight.NONE);
    assertFalse(rule.isConstrained());
  }

  @Test
  public void testPropertiesTwo() {
    // f(λx.Z⟨x⟩) → g( ⦇1,2⦈ ) with f a variable
    Term f = TermFactory.createVar("f", type("(o → o) → o"));
    Variable x = TermFactory.createBinder("x", type("o"));
    MetaVariable z = TermFactory.createMetaVar("Z", type("o → o"), 1);
    Term g = TermFactory.createConstant("g", type("⦇ Int , Int ⦈ → o"));
    Term tuple =
      TermFactory.createTuple(TheoryFactory.createValue(1), TheoryFactory.createValue(2));
    Term left = f.apply(TermFactory.createAbstraction(x, TermFactory.createMeta(z, x)));
    Term right = g.apply(tuple);
    Rule rule = new Rule(left, right);
    RuleRestrictions properties = rule.queryProperties();
    assertTrue(properties.queryLevel() == Level.META);
    assertTrue(properties.theoriesUsed());
    assertTrue(properties.productsUsed());
    assertTrue(properties.patternStatus() == Lhs.SEMIPATTERN);
    assertTrue(properties.rootStatus() == Root.ANY);
    assertTrue(properties.rightReplaceablePolicy() == FreshRight.NONE);
    assertFalse(rule.isConstrained());
  }

  @Test
  public void testPropertiesThree() {
    // +(a, Z⟨1⟩) → x | x > 0
    Term a = TermFactory.createConstant("a", type("Int"));
    MetaVariable z = TermFactory.createMetaVar("Z", type("Int → Int"), 1);
    Term z1 = TermFactory.createMeta(z, TheoryFactory.createValue(1));
    Term left = TheoryFactory.plusSymbol.apply(a).apply(z1);
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(TheoryFactory.createValue(0));
    Rule rule = new Rule(left, x, constraint);
    RuleRestrictions properties = rule.queryProperties();
    assertTrue(properties.queryLevel() == Level.META);
    assertTrue(properties.theoriesUsed());
    assertFalse(properties.productsUsed());
    assertTrue(properties.patternStatus() == Lhs.NONPATTERN);
    assertTrue(properties.rootStatus() == Root.THEORY);
    assertTrue(properties.rightReplaceablePolicy() == FreshRight.CVARS);
    assertTrue(rule.isConstrained());
  }

  @Test
  public void testConstraintNotBool() {
    // f(x) → x | x
    Term f = TermFactory.createConstant("f", type("Int → Int"));
    Variable x = TermFactory.createVar("x", type("Int"));
    assertThrows(IllegalRuleException.class, () -> new Rule(f.apply(x), x, x));
  }

  @Test
  public void testConstraintNotTheory() {
    // f(x) → x | x > a
    Term a = TermFactory.createConstant("a", type("Int"));
    Term f = TermFactory.createConstant("f", type("Int → Int"));
    Variable x = TermFactory.createVar("x", type("Int"));
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(a);
    assertThrows(IllegalRuleException.class, () -> new Rule(f.apply(x), x, constraint));
  }

  @Test
  public void testConstraintWithNonTheoryVariable() {
    // f(x) → x | x > 1 where x has type Int, but it is not marked as a theory sort
    Term f = TermFactory.createConstant("f", type("Int → Int"));
    Variable x = TermFactory.createVar("x", TypeFactory.createSort("Int"));
    Term one = TheoryFactory.createValue(1);
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(one);
    assertThrows(IllegalRuleException.class, () -> new Rule(f.apply(x), x, constraint));
  }

  @Test
  public void testConstraintWithBinder() {
    // f(x) → x | x > 1 where x is a binder
    Term f = TermFactory.createConstant("f", type("Int → Int"));
    Variable x = TermFactory.createBinder("x", type("Int"));
    Term one = TheoryFactory.createValue(1);
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(one);
    assertThrows(IllegalRuleException.class, () -> new Rule(f.apply(x), x, constraint));
  }

  @Test
  public void testConstraintWithLambda() {
    // f(x) → x | x > (λy.y)(1)
    Term f = TermFactory.createConstant("f", type("Int → Int"));
    Variable x = TermFactory.createVar("x", type("Int"));
    Term one = TheoryFactory.createValue(1);
    Variable y = TermFactory.createBinder("y", type("Int"));
    Term abs = TermFactory.createAbstraction(y, y);
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(abs.apply(one));
    assertThrows(IllegalRuleException.class, () -> new Rule(f.apply(x), x, constraint));
  }

  @Test
  public void testConstraintWithFreshVariable() {
    // f(x) → x | x > y
    Term f = TermFactory.createConstant("f", type("Int → Int"));
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(y);
    Rule rule = new Rule(f.apply(x), x, constraint);
    assertTrue(rule.toString().equals("f(x) → x | x > y"));
    assertTrue(rule.queryLVars().size() == 2);
    assertTrue(rule.queryLVars().contains(x));
    assertTrue(rule.queryLVars().contains(y));
    assertTrue(rule.isConstrained());
    assertTrue(rule.queryProperties().theoriesUsed());
  }

  @Test
  public void testLVars() {
    // f(x) → y | x > y
    Term f = TermFactory.createConstant("f", type("Int → Int"));
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(y);
    Rule rule = new Rule(f.apply(x), y, constraint);
    assertTrue(rule.toString().equals("f(x) → y | x > y"));
    assertTrue(rule.queryLVars().size() == 2);
    assertTrue(rule.queryLVars().contains(x));
    assertTrue(rule.queryLVars().contains(y));
    assertTrue(rule.isConstrained());
    assertTrue(rule.queryProperties().theoriesUsed());
    Variable z = TermFactory.createVar("z", type("Int"));
    assertThrows(java.lang.UnsupportedOperationException.class, () -> rule.queryLVars().add(z));
    assertTrue(rule.queryLVars().size() == 2);

    // f(x) -> y
    Rule rule2 = new Rule(f.apply(x), y);
    assertTrue(rule2.queryLVars().size() == 0);
    assertThrows(java.lang.UnsupportedOperationException.class, () -> rule2.queryLVars().add(z));
  }

  @Test
  public void testTVars() {
    // f(x) -> f(y) | x > z ∧ z > y
    Term f = TermFactory.createConstant("f", type("Int → Int"));
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Variable z = TermFactory.createVar("y", type("Int"));
    Term l = f.apply(x);
    Term r = f.apply(y);
    Term xz = TheoryFactory.greaterSymbol.apply(x).apply(z);
    Term zy = TheoryFactory.greaterSymbol.apply(z).apply(y);
    Term c = TheoryFactory.createConjunction(xz, zy);
    Rule rule = new Rule(l, r, c);
    assertTrue(rule.queryLVars().size() == 3);
    java.util.Set<Variable> tvar = rule.queryTVars();
    assertTrue(tvar.size() == 2);
    assertTrue(tvar.contains(x));
    assertTrue(tvar.contains(y));
    assertFalse(tvar.contains(z));
    assertThrows(java.lang.UnsupportedOperationException.class, () -> tvar.add(z));
  }

  @Test
  public void testAllReplaceables() {
    // f(x,a) -> f(y,G[b]) | x > z ∧ z > y
    Term f = TermFactory.createConstant("f", type("Int → Int → Int"));
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Variable z = TermFactory.createVar("y", type("Int"));
    Variable a = TermFactory.createVar("a", type("Int"));
    Variable b = TermFactory.createVar("b", type("Int"));
    MetaVariable g = TermFactory.createMetaVar("G", type("Int"), type("Int"));
    Term gb = TermFactory.createMeta(g, b);
    Term l = f.apply(x).apply(a);
    Term r = f.apply(y).apply(gb);
    Term xz = TheoryFactory.greaterSymbol.apply(x).apply(z);
    Term zy = TheoryFactory.greaterSymbol.apply(z).apply(y);
    Term c = TheoryFactory.createConjunction(xz, zy);
    Rule rule = new Rule(l, r, c);
    Set<Replaceable> set = rule.queryAllReplaceables();
    assertTrue(set.size() == 6);
    assertTrue(set.contains(x));
    assertTrue(set.contains(y));
    assertTrue(set.contains(z));
    assertTrue(set.contains(a));
    assertTrue(set.contains(b));
    assertTrue(set.contains(g));
  }

  @Test
  public void testLhsTheory() {
    // x + 0 → x
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term lhs = TheoryFactory.plusSymbol.apply(x).apply(TheoryFactory.createValue(0));
    assertThrows(IllegalRuleException.class, () -> new Rule(lhs, x));
  }

  @Test
  public void testLhsPotentiallyTheory() {
    // +((λx.Z[f(x)])(0), y)
    Variable x = TermFactory.createBinder("x", TypeFactory.intSort);
    Term fx = makeConstant("f", "Int → Int").apply(x);
    MetaVariable z = TermFactory.createMetaVar("Z", type("Int → Int"), 1);
    Term zfx = TermFactory.createMeta(z, fx);
    Term abs = TermFactory.createAbstraction(x, zfx);
    Term abso = abs.apply(TheoryFactory.createValue(0));
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Term lhs = TheoryFactory.plusSymbol.apply(abso).apply(y);
    assertThrows(IllegalRuleException.class, () -> new Rule(lhs, y));
  }

  @Test
  public void testVariableNaming() {
    // f(x, y) → g(y, λz.z) | x -- except all variables have the same default name
    Variable x = TermFactory.createVar("x", type("Bool"));
    Variable y = TermFactory.createVar("x", type("b"));
    Variable z = TermFactory.createBinder("x", type("c"));
    FunctionSymbol f = makeConstant("f", "Bool → b → d");
    FunctionSymbol g = makeConstant("g", "b → (c → c) → d");
    Term left = TermFactory.createApp(f, x, y);
    Term right = TermFactory.createApp(g, y, TermFactory.createAbstraction(z, z));
    Rule rule = new Rule(left, right, x);
    assertTrue(rule.toString().equals("f(x__1, x__2) → g(x__2, λx1.x1) | x__1"));
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
    Rule rule = new Rule(left, y);
    assertTrue(rule.queryLeftSide().equals(left));
    assertTrue(rule.queryRightSide().equals(y));
    assertTrue(rule.queryType().equals(type("u")));
    assertTrue(rule.toString().equals("f(λx.x(a), y) → y"));
    assertFalse(rule.isApplicative());
    assertTrue(rule.isPatternRule());

    rule = new Rule(y, y);
    assertTrue(rule.toString().equals("y → y"));
    assertTrue(rule.isApplicative());
    assertTrue(rule.isPatternRule());
    assertFalse(rule.queryTermFunctionRoot());
    assertTrue(rule.isLeftLinear());
  }

  @Test
  public void testNotLinear() {
    // f(x, x) - x | x > 0
    Variable x = TermFactory.createVar("x", type("Int"));
    Term f = makeConstant("f", "Int -> Int -> Int");
    Term left = TermFactory.createApp(f, x, x);
    Term zero = TheoryFactory.createValue(0);
    Term constraint = TermFactory.createApp(TheoryFactory.greaterSymbol, x, zero);
    Rule rule = new Rule(left, x, constraint);
    assertFalse(rule.isLeftLinear());
  }
}

