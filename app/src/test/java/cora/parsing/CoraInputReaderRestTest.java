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

package cora.parsing;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.exceptions.ParseError;
import cora.types.Type;
import cora.types.TypeFactory;
import cora.terms.Term;
import cora.terms.TermFactory;
import cora.rewriting.Rule;
import cora.rewriting.TRS;
import cora.parsing.lib.ErrorCollector;
import cora.parsing.lib.ParsingStatus;

public class CoraInputReaderRestTest {
  private ParsingStatus makeStatus(String text, ErrorCollector collector) {
    return new ParsingStatus(CoraTokenData.getUnconstrainedStringLexer(text), collector);
  }

  private ParsingStatus makeConstrainedStatus(String text, ErrorCollector collector) {
    return new ParsingStatus(CoraTokenData.getConstrainedStringLexer(text), collector);
  }

  private SymbolData makeBasicData() {
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(
      TermFactory.createConstant("f", CoraInputReader.readTypeFromString("a ⇒ b")));
    data.addFunctionSymbol(
      TermFactory.createConstant("aa", CoraInputReader.readTypeFromString("a")));
    data.addFunctionSymbol(
      TermFactory.createConstant("bb", CoraInputReader.readTypeFromString("b")));
    data.addFunctionSymbol(
      TermFactory.createConstant("h", CoraInputReader.readTypeFromString("a ⇒ b ⇒ b")));
    data.addFunctionSymbol(
      TermFactory.createConstant("i", CoraInputReader.readTypeFromString("b ⇒ a")));
    data.addFunctionSymbol(TermFactory.createConstant("map",
      CoraInputReader.readTypeFromString("(nat -> nat) -> list -> list")));
    data.addFunctionSymbol(TermFactory.createConstant("cons",
      CoraInputReader.readTypeFromString("nat -> list -> list")));
    return data;
  }

  @Test
  public void testMixedEnvironment() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("{ x :: a, y :: [b,c] -> d } aa → aa", collector);
    SymbolData data = makeBasicData();
    assertTrue(CoraInputReader.readRuleForUnitTest(status, data).toString().equals("aa → aa"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("a"));
    assertTrue(data.lookupMetaVariable("y").queryType().toString().equals("b ⇒ c ⇒ d"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testEnvironmentWithVariableAlreadyDeclaredAsFunctionSymbol() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("{ aa :: b } aa → aa", collector);
    SymbolData data = makeBasicData();
    Rule rule = CoraInputReader.readRuleForUnitTest(status, data);
    assertTrue(rule.toString().equals("aa → aa"));
    assertTrue(rule.queryLeftSide().isConstant());
    assertTrue(rule.queryLeftSide().queryType().toString().equals("a"));
    assertTrue(data.lookupVariable("aa") == null);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:3: Name of variable aa already occurs as a function symbol.\n"));
  }

  @Test
  public void testCorrectFirstOrderRule() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("h(x, y) -> h(x, h(aa, y))", collector);
    SymbolData data = makeBasicData();
    Rule rule = CoraInputReader.readRuleForUnitTest(status, data);
    assertTrue(rule.toString().equals("h(x, y) → h(x, h(aa, y))"));
    assertTrue(rule.queryLeftSide().vars().size() == 2);
    assertTrue(rule.queryLeftSide().queryType().toString().equals("b"));
    assertTrue(rule.isFirstOrder());
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testApplicativeRuleWithHeadVariable() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("{ F :: a -> a } h(F(aa), bb) -> f(F(i(bb)))", collector);
    SymbolData data = makeBasicData();
    Rule rule = CoraInputReader.readRuleForUnitTest(status, data);
    assertTrue(rule.toString().equals("h(F(aa), bb) → f(F(i(bb)))"));
    assertTrue(rule.queryLeftSide().vars().size() == 1);
    assertFalse(rule.queryLeftSide().isPattern());
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testCreatePatternRule() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("map(λx.F[x], cons(H, T)) → " +
                                      "cons(F[H], map(λx::nat.F[x], T))", collector);
    SymbolData data = makeBasicData();
    Rule rule = CoraInputReader.readRuleForUnitTest(status, data);
    assertTrue(rule.toString().equals("map(λx.F⟨x⟩, cons(H, T)) → cons(F⟨H⟩, map(λx.F⟨x⟩, T))"));
    assertTrue(rule.queryLeftSide().mvars().size() == 3);
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testCreateNonPatternRule() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus(
      "{ F :: [nat,nat] ⇒ nat } map(λx.F[X,Y[x]], cons(x, y)) -> cons(Y[x],y)", collector);
    SymbolData data = makeBasicData();
    Rule rule = CoraInputReader.readRuleForUnitTest(status, data);
    assertTrue(rule.toString().equals("map(λx1.F⟨X, Y⟨x1⟩⟩, cons(x, y)) → cons(Y⟨x⟩, y)"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testCreateFirstOrderConstrainedRule() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeConstrainedStatus(
      "sum(x) -> x + sum(x-1) | x > 0", collector);
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(
      TermFactory.createConstant("sum", CoraInputReader.readTypeFromString("Int ⇒ Int")));
    Rule rule = CoraInputReader.readRuleForUnitTest(status, data);
    assertTrue(rule.isConstrained());
    assertTrue(rule.toString().equals("sum(x) → x + sum(x - 1) | x > 0"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testCreateHigherOrderConstrainedRule() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeConstrainedStatus(
      "rec(F, x, y) → F(x, y, rec(F, x-1, y)) | x > 0", collector);
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(TermFactory.createConstant("rec",
      CoraInputReader.readTypeFromString("(Int ⇒ Int ⇒ Int ⇒ Int) ⇒ Int ⇒ Int ⇒ Int")));
    Rule rule = CoraInputReader.readRuleForUnitTest(status, data);
    assertTrue(rule.isConstrained());
    assertTrue(rule.toString().equals("rec(F, x, y) → F(x, y, rec(F, x - 1, y)) | x > 0"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testRuleWithComplexConstraint() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeConstrainedStatus(
      "app(F,x) -> F(x)|0 <= x ∧ (x < 10 ∨ x = 13)", collector);
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(TermFactory.createConstant("app",
      CoraInputReader.readTypeFromString("(Int ⇒ Int) ⇒ Int ⇒ Int")));
    Rule rule = CoraInputReader.readRuleForUnitTest(status, data);
    assertTrue(rule.toString().equals("app(F, x) → F(x) | 0 ≤ x ∧ (x < 10 ∨ x = 13)"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testRuleWithHigherVariableInConstraint() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeConstrainedStatus(
      "filter(F,cons(H,T)) -> cons(H, filter(F, T)) | F(H)", collector);
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(TermFactory.createConstant("cons",
      CoraInputReader.readTypeFromString("Int ⇒ List ⇒ List")));
    data.addFunctionSymbol(TermFactory.createConstant("filter",
      CoraInputReader.readTypeFromString("(Int ⇒ Bool) ⇒ List ⇒ List")));
    Rule rule = CoraInputReader.readRuleForUnitTest(status, data);
    assertTrue(rule == null);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:1: constraint [F(H)] contains a variable F of type Int ⇒ Bool; only " +
      "variables of theory sort are allowed to occur in a constraint.\n"));
  }

  @Test
  public void testUnconstrainedRuleWithFreshVariableInRhs() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus(" f(x) -> y", collector);
    SymbolData data = makeBasicData();
    Rule rule = CoraInputReader.readRuleForUnitTest(status, data);
    assertTrue(rule == null);
    assertTrue(collector.queryCollectedMessages().equals("1:2: right-hand side of rule " +
      "[f(x) → y] contains fresh variable y of type b, which is not a theory sort.\n"));
  }

  @Test
  public void testRuleWithFreshVariableInConstraint() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeConstrainedStatus("random(x) → y | 0 <= x ∧ y < x", collector);
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(TermFactory.createConstant("random",
      CoraInputReader.readTypeFromString("Int ⇒ Int")));
    Rule rule = CoraInputReader.readRuleForUnitTest(status, data);
    assertTrue(rule.toString().equals("random(x) → y | 0 ≤ x ∧ y < x"));
  }

  @Test
  public void testRuleWithFreshTheoryVariableInRhs() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeConstrainedStatus("random → x", collector);
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(TermFactory.createConstant("random",
      CoraInputReader.readTypeFromString("Int")));
    Rule rule = CoraInputReader.readRuleForUnitTest(status, data);
    assertTrue(rule.toString().equals("random → x"));
  }

  @Test
  public void testRuleWithFreshNonTheoryVariableInRhs() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeConstrainedStatus("random → x", collector);
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(TermFactory.createConstant("random",
      CoraInputReader.readTypeFromString("Nat")));
    Rule rule = CoraInputReader.readRuleForUnitTest(status, data);
    assertTrue(rule == null);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:1: right-hand side of rule [random → x] contains fresh variable x of type Nat, " +
      "which is not a theory sort.\n"));
  }

  @Test
  public void testRuleTypeError() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("aa ->bb", collector);
    SymbolData data = makeBasicData();
    Rule rule = CoraInputReader.readRuleForUnitTest(status, data);
    assertTrue(rule.toString().equals("aa → bb"));
    assertTrue(collector.queryCollectedMessages().equals("1:6: Expected term of type a, " +
      "but got function symbol bb which has type b.\n"));
  }

  @Test
  public void testShortFirstOrderProgram() {
    TRS trs = CoraInputReader.readProgramFromString(
      "0 :: N s :: N -> N add :: N -> N -> N add(0,y) -> y add(s(x),y) -> s(add(x,y))",
      CoraInputReader.MSTRS);
    assertTrue(trs.lookupSymbol("0").queryType().toString().equals("N"));
    assertTrue(trs.lookupSymbol("s").queryType().toString().equals("N ⇒ N"));
    assertTrue(trs.lookupSymbol("add").queryType().toString().equals("N ⇒ N ⇒ N"));
    assertTrue(trs.queryRule(0).toString().equals("add(0, y) → y"));
    assertTrue(trs.queryRule(1).toString().equals("add(s(x), y) → s(add(x, y))"));
  }

  @Test
  public void testWeirdProgram() {
    TRS trs = CoraInputReader.readProgramFromString(
      "f :: a -> a -> a b :: b f(x,x) -> x b -> b c :: a",
      CoraInputReader.MSTRS);
    assertTrue(trs.lookupSymbol("f").queryType().toString().equals("a ⇒ a ⇒ a"));
    assertTrue(trs.lookupSymbol("b").queryType().toString().equals("b"));
    assertTrue(trs.lookupSymbol("c").queryType().toString().equals("a"));
    assertTrue(trs.queryRule(0).toString().equals("f(x, x) → x"));
    assertTrue(trs.queryRule(1).toString().equals("b → b"));
  }

  @Test
  public void testApplicativeNonPatternTRS() {
    TRS trs = CoraInputReader.readProgramFromString(
      "3 :: Int 7 :: Int f :: Bool -> Int -> Bool\n" +
      "{X :: Int -> Int -> Int -> Bool} f(X(3,y,7), y) -> X(7,3,y)",
      CoraInputReader.STRS);
    assertTrue(trs.lookupSymbol("3").queryType().toString().equals("Int"));
    assertTrue(trs.lookupSymbol("7").queryType().toString().equals("Int"));
    assertTrue(trs.lookupSymbol("f").queryType().toString().equals("Bool ⇒ Int ⇒ Bool"));
    assertTrue(trs.queryRule(0).toString().equals("f(X(3, y, 7), y) → X(7, 3, y)"));
    assertFalse(trs.queryRule(0).isPatternRule());
  }

  @Test
  public void testNoVariableConflictsBetweenRules() {
    TRS trs = CoraInputReader.readProgramFromString(
        "f :: a -> a  g :: b -> b f(x) -> x  g(x) -> x");
    assertTrue(!trs.queryRule(0).queryRightSide().equals(trs.queryRule(1).queryRightSide()));
  }

  @Test
  public void testSTRSWithUndeclaredVariable() {
    try {
      TRS trs = CoraInputReader.readProgramFromString(
        "3 :: Int 7 :: Int f :: Bool -> Int -> Bool\n" +
        "f(X(3,y,7), y) -> X(7,3,y)", CoraInputReader.AMS);
    }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "2:3: Undeclared symbol: X.  Type cannot easily be deduced from context.\n" +
        "2:19: Undeclared symbol: X.  Type cannot easily be deduced from context.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadRuleWithInconsistentTypes() {
    try {
      TRS trs = CoraInputReader.readProgramFromString("a :: type1 b :: type2 a -> b");
    }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals("1:28: Expected term of type type1, but got function " +
        "symbol b which has type type2.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testMultipleErrorsWithRules() {
    try {
      TRS trs = CoraInputReader.readProgramFromString(
        "f :: nat -> nat\n" +
        "2 :: nat\n" +
        "f(x) -> g(2,x)\n" +
        "a :: 3\n" +
        "g(a,y) -> a -> y\n" +
        "f(2) -> 3\n", CoraInputReader.AMS);
    }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "3:9: Undeclared symbol: g.  Type cannot easily be deduced from context.\n" +
        "5:1: Undeclared symbol: g.  Type cannot easily be deduced from context.\n" +
        "5:11: Expected term of type o, but got function symbol a which has type 3.\n" +
        "5:13: Expected term, started by an identifier, λ, string or (, but got ARROW (->).\n" +
        "6:1: right-hand side of rule [f(2) → 3] contains fresh variable 3 of type nat, which " +
          "is not a theory sort.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testMultipleErrorsWithConstrainedRules() {
    try {
      TRS trs = CoraInputReader.readProgramFromString(
        "f :: Int -> Int\n" +
        "f(x) -> f(x + 2 | x < 0 \n" +
        "f(x) -> x | x > 0)\n" +
        "f(2) -> 3\n" +
        "- :: Int -> Int -> Int\n" +
        "f(3) -> 4 | true \n" +
        "-(x, y) -> x + -1 * y\n",
        CoraInputReader.LCSTRS);
    }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "2:17: Expected a comma or closing bracket ) but got MID (|).\n" +
        "3:18: Expected term, started by an identifier, λ, string or (, but got " +
          "BRACKETCLOSE ()).\n" +
        "5:3: Expected term, started by an identifier, λ, string or (, but got DECLARE (::).\n" +
        "7:4: Expected a closing bracket but got COMMA (,).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testNotFirstOrderDueToSymbol() {
    try {
      TRS trs = CoraInputReader.readProgramFromString(
        "f :: nat -> nat g :: (nat -> nat) -> nat f(x) → x", CoraInputReader.MSTRS);
    }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "Symbol with a type (nat ⇒ nat) ⇒ nat cannot occur in a many-sorted TRS.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testNotFirstOrderDueToRule() {
    try {
      TRS trs = CoraInputReader.readProgramFromString(
        "f :: nat -> nat { F :: nat -> nat } f(F(x)) → x", CoraInputReader.MSTRS);
    }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "Rule f(F(x)) → x cannot occur in a many-sorted TRS, as it is not first-order.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testNotApplicative() {
    try {
      TRS trs = CoraInputReader.readProgramFromString(
        "f :: (nat -> nat) -> nat f(F) → f(λx.F(x))", CoraInputReader.STRS);
    }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals("Rule f(F) → f(λx.F(x)) cannot occur in an applicative " +
        "(simply-typed) TRS, as it is not applicative.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testNotCFS() {
    try {
      TRS trs = CoraInputReader.readProgramFromString(
        "map :: (nat -> nat) -> list -> list nil :: list map(λx.Z[x], nil) → nil",
        CoraInputReader.CFS);
    }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals("Rule map(λx.Z⟨x⟩, nil) → nil cannot occur in " +
        "a Curried Functional System, as it contains meta-variables.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadAMS() {
    TRS trs = CoraInputReader.readProgramFromString(
      "map :: (nat -> nat) -> list -> list nil :: list map(λx.Z[x], nil) → nil",
      CoraInputReader.AMS);
    assertTrue(trs.queryRule(0).queryLeftSide().isPattern());
  }
}

