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

package cora.reader;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import java.util.ArrayList;
import java.util.TreeSet;

import cora.exceptions.ParseError;
import cora.types.Type;
import cora.parser.lib.ErrorCollector;
import cora.parser.CoraParser;
import cora.types.Type;
import cora.types.TypeFactory;
import cora.terms.*;
import cora.trs.*;

public class CoraInputReaderTest {
  private Type type(String str) {
    return CoraParser.readType(str);
  }

  private SymbolData makeBasicData() {
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(TermFactory.createConstant("f", type("a → Int")));
    data.addFunctionSymbol(TermFactory.createConstant("aa", type("a")));
    data.addFunctionSymbol(TermFactory.createConstant("bb", type("Int")));
    data.addFunctionSymbol(TermFactory.createConstant("h", type("a → Int → Int")));
    data.addFunctionSymbol(TermFactory.createConstant("i", type("Int → a")));
    data.addFunctionSymbol(TermFactory.createConstant("map", type("(nat → nat) → list → list")));
    data.addFunctionSymbol(TermFactory.createConstant("cons", type("nat → list → list")));
    return data;
  }

  private TRS createEmptyTRS(Alphabet alphabet) {
    return TrsFactory.createTrs(alphabet, new ArrayList<Rule>(), TrsFactory.CORA);
  }

  private TRS generateTRS() {
    SymbolData data = makeBasicData();
    Alphabet alphabet = data.queryCurrentAlphabet();
    return createEmptyTRS(alphabet);
  }

  @Test
  public void testCorrectDeclaration() {
    ErrorCollector collector = new ErrorCollector();
    SymbolData data = new SymbolData();
    CoraInputReader.readDeclarationForUnitTest("public f :: a -> a", data, false, collector);
    CoraInputReader.readDeclarationForUnitTest("private g :: a -> a", data, false, collector);
    CoraInputReader.readDeclarationForUnitTest("h :: a -> a", data, false, collector);
    assertTrue(data.queryPrivateSymbols().size() == 1);
    assertTrue(data.queryPrivateSymbols().contains("g"));
  }

  @Test
  public void testDeclarationWithPreviouslyDeclaredName() {
    ErrorCollector collector = new ErrorCollector();
    SymbolData data = makeBasicData();
    String str = "f :: a -> (b -> c)";
    CoraInputReader.readDeclarationForUnitTest(str, data, true, collector);
    assertTrue(data.lookupFunctionSymbol("f").queryType().toString().equals("a → Int"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:1: Redeclaration of previously declared function symbol f.\n"));
  }

  @Test
  public void testPublicPrivateStored() {
    ErrorCollector collector = new ErrorCollector();
    SymbolData data = makeBasicData();
    String str = "f :: a -> (b -> c)";
    CoraInputReader.readDeclarationForUnitTest(str, data, true, collector);
    assertTrue(data.lookupFunctionSymbol("f").queryType().toString().equals("a → Int"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:1: Redeclaration of previously declared function symbol f.\n"));
  }

  @Test
  public void testRuleWithVariableEnvironment() {
    Rule rule = CoraInputReader.readRule("{ F :: a -> a } f(F(x)) → y", generateTRS());
    assertTrue(rule.toString().equals("f(F(x)) → y"));
    Variable f = rule.queryLeftSide().queryArgument(1).queryHead().queryVariable();
    assertTrue(f.queryType().toString().equals("a → a"));
    Variable x = rule.queryLeftSide().queryArgument(1).queryArgument(1).queryVariable();
    assertTrue(x.queryType().toString().equals("a"));
    assertTrue(rule.queryRightSide().queryVariable().queryType().toString().equals("Int"));
  }

  @Test
  public void testRuleWithMetavariableEnvironment() {
    Rule rule = CoraInputReader.readRule("{ F :: [a] -> a } f(F[x]) → y", generateTRS());
    assertTrue(rule.toString().equals("f(F⟨x⟩) → y"));
    MetaVariable f = rule.queryLeftSide().queryArgument(1).queryHead().queryMetaVariable();
    assertTrue(f.queryType().toString().equals("a → a"));
    Variable x = rule.queryLeftSide().queryArgument(1).queryMetaArgument(1).queryVariable();
    assertTrue(x.queryType().toString().equals("a"));
  }

  @Test
  public void testRuleWithIncorrecTypeInEnvironment() {
    try { CoraInputReader.readRule("{ F :: Int -> Int } f(F(x)) → y", generateTRS()); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:23: Type error: expected term of type a, but got F(x) of type Int.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testAbuseVariableAsMetaVariable() {
    try { CoraInputReader.readRule("{ F :: a -> a } f(F[x]) → y", generateTRS()); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:19: Unexpected meta-application with meta-variable F, which was previously used " +
          "(or declared) as a variable without meta-arguments.\n" +
        "1:21: Undeclared symbol: x.  Type cannot easily be deduced from context.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testAbuseMetaVariableAsVariable() {
    try { CoraInputReader.readRule("{ F :: [a] -> a } f(F(x)) → y", generateTRS()); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:21: Symbol F was previously used (or declared) as a meta-variable with arity > 0; " +
        "here it is used as a variable.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testEnvironmentWithVariableAlreadyDeclaredAsFunctionSymbol() {
    try { CoraInputReader.readRule("{ aa :: b } aa → aa", generateTRS()); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:3: Name of variable aa already occurs as a function symbol.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testEnvironmentWithDuplicateVariableDeclaration() {
    try { CoraInputReader.readRule("{ x :: type, x :: type } aa → aa", generateTRS()); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:14: Redeclaration of variable x in the same environment.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testEnvironmentWithDuplicateMetaVariableDeclaration() {
    try { CoraInputReader.readRule("{ x :: type, x :: [type] -> type } aa → aa", generateTRS()); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:14: Redeclaration of meta-variable x in the same environment.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testCorrectFirstOrderRule() {
    Rule rule = CoraInputReader.readRule("h(x, y) -> h(x, h(aa, y))", generateTRS());
    assertTrue(rule.toString().equals("h(x, y) → h(x, h(aa, y))"));
    assertTrue(rule.queryLeftSide().vars().size() == 2);
    assertTrue(rule.queryLeftSide().queryType().equals(TypeFactory.intSort));
    assertTrue(rule.isFirstOrder());
  }

  @Test
  public void testApplicativeRuleWithHeadVariable() {
    Rule rule =
      CoraInputReader.readRule("{ F :: a -> a } h(F(aa), bb) -> f(F(i(bb)))", generateTRS());
    assertTrue(rule.toString().equals("h(F(aa), bb) → f(F(i(bb)))"));
    assertTrue(rule.queryLeftSide().vars().size() == 1);
    assertFalse(rule.queryLeftSide().isPattern());
  }

  @Test
  public void testCreatePatternRule() {
    Rule rule = CoraInputReader.readRule("map(λx.F[x], cons(H, T)) → " +
                                         "cons(F[H], map(λx::nat.F[x], T))", generateTRS());
    assertTrue(rule.toString().equals("map(λx.F⟨x⟩, cons(H, T)) → cons(F⟨H⟩, map(λx.F⟨x⟩, T))"));
    assertTrue(rule.queryLeftSide().mvars().size() == 3);
  }

  @Test
  public void testCreateNonPatternRule() {
    Rule rule = CoraInputReader.readRule(
      "{ F :: [nat,nat] → nat } map(λx.F[X,Y[x]], cons(x, y)) -> cons(Y[x],y)", generateTRS());
    assertTrue(rule.toString().equals("map(λx1.F⟨X, Y⟨x1⟩⟩, cons(x, y)) → cons(Y⟨x⟩, y)"));
  }

  @Test
  public void testCreateFirstOrderConstrainedRule() {
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(TermFactory.createConstant("sum", type("Int → Int")));
    Alphabet alphabet = data.queryCurrentAlphabet();
    TRS trs = createEmptyTRS(alphabet);
    Rule rule = CoraInputReader.readRule("sum(x) -> x + sum(x-1) | x > 0", trs);
    assertTrue(rule.isConstrained());
    assertTrue(rule.toString().equals("sum(x) → x + sum(x - 1) | x > 0"));
  }

  @Test
  public void testCreateHigherOrderConstrainedRule() {
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(TermFactory.createConstant("rec",
      type("(Int → Int → Int → Int) → Int → Int → Int")));
    Alphabet alphabet = data.queryCurrentAlphabet();
    TRS trs = createEmptyTRS(alphabet);
    Rule rule = CoraInputReader.readRule("rec(F, x, y) → F(x, y, rec(F, x-1, y)) | x > 0", trs);
    assertTrue(rule.isConstrained());
    assertTrue(rule.toString().equals("rec(F, x, y) → F(x, y, rec(F, x - 1, y)) | x > 0"));
  }

  @Test
  public void testRuleWithComplexConstraint() {
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(TermFactory.createConstant("app", type("(Int → Int) → Int → Int")));
    Alphabet alphabet = data.queryCurrentAlphabet();
    TRS trs = createEmptyTRS(alphabet);
    Rule rule = CoraInputReader.readRule("app(F,x) -> F(x)|0 <= x ∧ (x < 10 ∨ x = 13)", trs);
    assertTrue(rule.toString().equals("app(F, x) → F(x) | 0 ≤ x ∧ (x < 10 ∨ x = 13)"));
  }

  @Test
  public void testRuleWithHigherVariableInConstraint() {
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(TermFactory.createConstant("cons",type("Int → List → List")));
    data.addFunctionSymbol(TermFactory.createConstant("filter",type("(Int → Bool) → List → List")));
    Alphabet alphabet = data.queryCurrentAlphabet();
    TRS trs = createEmptyTRS(alphabet);
    try { CoraInputReader.readRule("filter(F,cons(H,T)) -> cons(H, filter(F, T)) | F(H)", trs); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals("1:1: constraint [F(H)] is not first-order.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testUnconstrainedRuleWithFreshVariableInRhs() {
    try { CoraInputReader.readRule(" i(x) -> y", generateTRS()); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals("1:2: right-hand side of rule [i(x) → y] " +
        "contains variable y of type a which does not occur on the left; only " +
        "variables of theory sorts may occur fresh (and that only in some kinds " +
        "of TRSs).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testRuleWithFreshVariableInConstraint() {
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(TermFactory.createConstant("random",  type("Int -> Int")));
    Alphabet alphabet = data.queryCurrentAlphabet();
    TRS trs = createEmptyTRS(alphabet);
    Rule rule = CoraInputReader.readRule("random(x) → y | 0 <= x ∧ y < x", trs);
    assertTrue(rule.toString().equals("random(x) → y | 0 ≤ x ∧ y < x"));
  }

  @Test
  public void testRuleWithFreshTheoryVariableInRhs() {
    Rule rule = CoraInputReader.readRule("f(x) -> y", generateTRS());
    assertTrue(rule.toString().equals("f(x) → y"));
  }

  @Test
  public void testRuleTypeError() {
    try { CoraInputReader.readRule("aa ->bb", generateTRS()); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals("1:6: Expected term of type a, " +
      "but got function symbol bb which has type Int.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testShortFirstOrderProgram() {
    TRS trs = CoraInputReader.readTrsFromString(
      "0 :: N s :: N -> N add :: N -> N -> N add(0,y) -> y add(s(x),y) -> s(add(x,y))",
      TrsFactory.MSTRS);
    assertTrue(trs.lookupSymbol("0").queryType().toString().equals("N"));
    assertTrue(trs.lookupSymbol("s").queryType().toString().equals("N → N"));
    assertTrue(trs.lookupSymbol("add").queryType().toString().equals("N → N → N"));
    assertTrue(trs.queryRule(0).toString().equals("add(0, y) → y"));
    assertTrue(trs.queryRule(1).toString().equals("add(s(x), y) → s(add(x, y))"));
  }

  @Test
  public void testWeirdProgram() {
    TRS trs = CoraInputReader.readTrsFromString(
      "public f :: a -> a -> a private b :: b f(x,x) -> x b -> b c :: a", TrsFactory.MSTRS);
    assertTrue(trs.lookupSymbol("f").queryType().toString().equals("a → a → a"));
    assertTrue(trs.lookupSymbol("b").queryType().toString().equals("b"));
    assertTrue(trs.lookupSymbol("c").queryType().toString().equals("a"));
    assertFalse(trs.isPrivate(trs.lookupSymbol("f")));
    assertTrue(trs.isPrivate(trs.lookupSymbol("b")));
    assertFalse(trs.isPrivate(trs.lookupSymbol("c")));
    assertTrue(trs.queryRule(0).toString().equals("f(x, x) → x"));
    assertTrue(trs.queryRule(1).toString().equals("b → b"));
  }

  @Test
  public void testApplicativeNonPatternTRS() {
    TRS trs = CoraInputReader.readTrsFromString(
      "3 :: Int 7 :: Int f :: Bool -> Int -> Bool\n" +
      "{X :: Int -> Int -> Int -> Bool} f(X(3,y,7), y) -> X(7,3,y)",
      TrsFactory.STRS);
    assertTrue(trs.lookupSymbol("3").queryType().toString().equals("Int"));
    assertTrue(trs.lookupSymbol("7").queryType().toString().equals("Int"));
    assertTrue(trs.lookupSymbol("f").queryType().toString().equals("Bool → Int → Bool"));
    assertTrue(trs.queryRule(0).toString().equals("f(X(3, y, 7), y) → X(7, 3, y)"));
    assertFalse(trs.queryRule(0).isPatternRule());
  }

  @Test
  public void testNoVariableConflictsBetweenRules() {
    TRS trs = CoraInputReader.readTrsFromString(
        "f :: a -> a  g :: b -> b f(x) -> x  g(x) -> x");
    assertTrue(!trs.queryRule(0).queryRightSide().equals(trs.queryRule(1).queryRightSide()));
  }

  @Test
  public void testSTRSWithUndeclaredVariable() {
    try {
      TRS trs = CoraInputReader.readTrsFromString(
        "3 :: Int 7 :: Int f :: Bool -> Int -> Bool\n" +
        "f(X(3,y,7), y) -> X(7,3,y)", TrsFactory.AMS);
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
      TRS trs = CoraInputReader.readTrsFromString("a :: type1 b :: type2 a -> b");
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
      TRS trs = CoraInputReader.readTrsFromString(
        "f :: nat -> nat\n" +
        "2 :: nat\n" +
        "f(x) -> g(2,x)\n" +
        "a :: 3\n" +
        "g(a,y) -> a -> y\n" +
        "f(2) -> 3\n", TrsFactory.AMS);
    }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "5:13: Expected term, started by an identifier, λ, string or (, but got ARROW (->).\n" +
        "3:9: Undeclared symbol: g.  Type cannot easily be deduced from context.\n" +
        "5:1: Undeclared symbol: g.  Type cannot easily be deduced from context.\n" +
        "5:11: Expected term of type o, but got function symbol a which has type 3.\n" +
        "6:1: right-hand side of rule [f(2) → 3] contains variable 3 of type nat which does " +
        "not occur on the left; only variables of theory sorts may occur fresh (and that only " +
        "in some kinds of TRSs).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testMultipleErrorsWithConstrainedRules() {
    try {
      TRS trs = CoraInputReader.readTrsFromString(
        "f :: Int -> Int\n" +
        "f(x) -> f(x + 2 | x < 0 \n" +
        "f(x) -> x | x > 0)\n" +
        "f(2) -> 3\n" +
        "- :: Int -> Int -> Int\n" +
        "f(3) -> 4 | true \n" +
        "-(x, y) -> x + -1 * y\n",
        TrsFactory.LCSTRS);
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
      TRS trs = CoraInputReader.readTrsFromString(
        "f :: nat -> nat g :: (nat -> nat) -> nat f(x) → x", TrsFactory.MSTRS);
    }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "Symbol g with a type (nat → nat) → nat cannot occur in a first-order TRS.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testNotFirstOrderDueToRule() {
    try {
      TRS trs = CoraInputReader.readTrsFromString(
        "f :: nat -> nat { F :: nat -> nat } f(F(x)) → x", TrsFactory.MSTRS);
    }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:17: The rule f(F(x)) → x is not allowed to occur in MSTRSs: rule level is " +
        "limited to first-order terms, not applicative terms.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testNotApplicative() {
    try {
      TRS trs = CoraInputReader.readTrsFromString(
        "f :: (nat -> nat) -> nat f(F) → f(λx.F(x))", TrsFactory.STRS);
    }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals("1:26: The rule f(F) → f(λx.F(x)) is not allowed to " +
        "occur in STRSs: rule level is limited to applicative terms, not true terms.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testNotCFS() {
    try {
      TRS trs = CoraInputReader.readTrsFromString(
        "map :: (nat -> nat) -> list -> list nil :: list map(λx.Z[x], nil) → nil",
        TrsFactory.CFS);
    }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals("1:49: The rule map(λx.Z⟨x⟩, nil) → nil is not allowed " +
        "to occur in CFSs: rule level is limited to true terms, not meta-terms.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadAMS() {
    TRS trs = CoraInputReader.readTrsFromString(
      "map :: (nat -> nat) -> list -> list nil :: list map(λx.Z[x], nil) → nil",
      TrsFactory.AMS);
    assertTrue(trs.queryRule(0).queryLeftSide().isPattern());
  }

  @Test
  public void testPrivateSymbol() {
    TRS trs = CoraInputReader.readTrsFromString(
      "public a :: Int private b :: Int c :: Int", TrsFactory.LCTRS);
    Alphabet alphabet = trs.queryAlphabet();
    FunctionSymbol a = alphabet.lookup("a");
    FunctionSymbol b = alphabet.lookup("b");
    FunctionSymbol c = alphabet.lookup("c");
    assertFalse(trs.isPrivate(a));
    assertTrue(trs.isPrivate(b));
    assertFalse(trs.isPrivate(c));
  }
}

