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

