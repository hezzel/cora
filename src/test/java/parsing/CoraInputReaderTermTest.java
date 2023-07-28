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
import cora.terms.*;
import cora.rewriting.Rule;
import cora.rewriting.TRS;
import cora.rewriting.TRSFactory;
import cora.parsing.lib.ErrorCollector;
import cora.parsing.lib.ParsingStatus;

public class CoraInputReaderTermTest {
  private ParsingStatus makeStatus(String text) {
    return new ParsingStatus(CoraTokenData.getStringLexer(text), 10);
  }

  private ParsingStatus makeStatus(String text, ErrorCollector collector) {
    return new ParsingStatus(CoraTokenData.getStringLexer(text), collector);
  }

  private Type type(String str) {
    return CoraInputReader.readTypeFromString(str);
  }

  private SymbolData generateSignature() {
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(TermFactory.createConstant("f", type("a ⇒ b ⇒ c ⇒ d")));
    data.addFunctionSymbol(TermFactory.createConstant("aa", type("a")));
    data.addFunctionSymbol(TermFactory.createConstant("bb", type("b")));
    data.addFunctionSymbol(TermFactory.createConstant("cc", type("c")));
    data.addFunctionSymbol(TermFactory.createConstant("h", type("(c ⇒ d) ⇒ b")));
    return data;
  }

  private TRS generateTRS() {
    return TRSFactory.createAMS(generateSignature().queryCurrentAlphabet(),
                                new ArrayList<Rule>(), false);
  }

  private Term readTerm(String txt, String expected, String message) {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus(txt + " NEXT", collector);
    Type type = expected == null ? null : CoraInputReader.readTypeFromString(expected);
    Term t = CoraInputReader.readTermForUnitTest(status, generateSignature(), type);
    assertTrue(status.nextToken().getText().equals("NEXT"));
    assertTrue(collector.queryCollectedMessages().equals(message));
    return t;
  }

  private Term readTermPrint(String txt, String expected, String message) {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus(txt, collector);
    Type type = expected == null ? null : CoraInputReader.readTypeFromString(expected);
    Term t = CoraInputReader.readTermForUnitTest(status, generateSignature(), type);
    System.out.println("t = " + t);
    System.out.println(collector.queryCollectedMessages());
    assertTrue(false);
    return null;
  }


  @Test
  public void testReadSingleString() {
    Term term = CoraInputReader.readTermFromString("\"hello world!\\n\"", generateTRS());
    assertTrue(term.queryType().toString().equals("String"));
    assertTrue(term.toString().equals("\"hello world!\\n\""));
  }

  @Test
  public void testReadMultipleStrings() {
    Term term = CoraInputReader.readTermFromString("\"hello\"\n \" world!\"", generateTRS());
    assertTrue(term.queryType().toString().equals("String"));
    assertTrue(term.toString().equals("\"hello world!\""));
  }

  @Test(expected = ParseError.class)
  public void testMoreThanAString() {
    Term term = CoraInputReader.readTermFromString("\"a\"b", generateTRS());
  }

  @Test
  public void testStringWithIllegalEscapeInIt() {
    Term t = readTerm("\"a\\xb\"", null,
      "1:1: Stray escape chacter at position 3 of string constant " +
      "(\\x is not an escape sequence).\n");
    assertTrue(t.toString().equals("\"a\\xb\""));
  }

  @Test
  public void testStringWithCorrectType() {
    Term t = readTerm("\"test\"", "String", "");
    assertTrue(t.queryType().toString().equals("String"));
  }

  @Test
  public void testStringWithIncorrectType() {
    Term t = readTerm(" \"test\"", "string",
      "1:2: Expected term of type string, but got a string constant " +
        "(which has type String).\n");
    assertTrue(t.queryType().toString().equals("string"));
    assertTrue(t.toString().equals("\"test\""));
  }

  @Test
  public void testReadUndeclaredVariableWithoutType() {
    Term t = readTerm("xx_yy", null,
      "1:1: Undeclared symbol: xx_yy.  Type cannot easily be deduced from context.\n");
    assertTrue(t.isVariable());
    assertFalse(t.queryVariable().isBinderVariable());
    assertTrue(t.queryType().equals(TypeFactory.unitSort));
  }

  @Test
  public void testReadUndeclaredVariableWithType() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("xx_yy next", collector);
    Term t = CoraInputReader.readTermForUnitTest(status, generateSignature(), type("a -> b"));
    assertTrue(t.isVariable());
    assertFalse(t.queryVariable().isBinderVariable());
    assertTrue(t.queryType().toString().equals("a ⇒ b"));
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(status.nextToken().toString().equals("1:7: next (IDENTIFIER)"));
  }

  @Test
  public void testReadDeclaredVariableWithoutType() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("x", collector);
    SymbolData data = generateSignature();
    Variable x = TermFactory.createVar("x", type("(a -> b) -> b"));
    data.addVariable(x);
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t == x);
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testReadDeclaredVariableWithCorrectType() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("x", collector);
    SymbolData data = generateSignature();
    Variable x = TermFactory.createVar("x", type("(a -> b) -> b"));
    data.addVariable(x);
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("(a ⇒ b) ⇒ b"));
    assertTrue(t == x);
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testReadDeclaredVariableWithIncorrectType() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("x", collector);
    SymbolData data = generateSignature();
    Variable x = TermFactory.createVar("x", type("(a -> b) -> b"));
    data.addVariable(x);
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("(a ⇒ b)"));
    assertFalse(t == x);
    assertTrue(t.isVariable());
    assertTrue(t.toString().equals("x"));
    assertTrue(t.queryType().toString().equals("a ⇒ b"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:1: Expected term of type a ⇒ b, but got x, which was previously used as a " +
      "variable of type (a ⇒ b) ⇒ b.\n"));
  }

  @Test
  public void testReadBaseConstantWithoutType() {
    Term t = CoraInputReader.readTermFromString("aa", generateTRS());
    assertTrue(t.equals(TermFactory.createConstant("aa", type("a"))));
  }

  @Test
  public void testReadBaseConstantWithGoodType() {
    Term t = readTerm("aa", "a", "");
    assertTrue(t.equals(TermFactory.createConstant("aa", type("a"))));
  }

  @Test
  public void testReadBaseConstantWithBadType() {
    Term t = readTerm("aa", "b", "1:1: Expected term of type b, " +
      "but got aa, which was declared as a function symbol of type a.\n");
    assertTrue(t.equals(TermFactory.createConstant("aa", type("b"))));
  }

  @Test
  public void testReadHigherOrderConstant() {
    Term t = readTerm("f", null, "");
    assertTrue(t.equals(TermFactory.createConstant("f", type("a ⇒ b ⇒ c ⇒ d"))));
  }

  @Test
  public void testReadDeclaredMetaVariableUsedAsVariableWithNoExpectedType() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("x", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("x", type("a ⇒ b"), 1));
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t.isVariable());
    assertTrue(t.queryType().equals(type("a ⇒ b")));
    assertTrue(t.toString().equals("x"));
  }

  @Test
  public void testReadDeclaredMetaVariableUsedAsVariableWithExpectedType() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("x", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("x", type("a ⇒ b"), 1));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("c"));
    assertTrue(t.isVariable());
    assertTrue(t.queryType().equals(type("c")));
    assertTrue(t.toString().equals("x"));
  }

  @Test
  public void testReadEmptyApplicationOfConstantWithType() {
    Term t = readTerm("bb()", "b", "");
    assertTrue(t.equals(TermFactory.createConstant("bb", type("b"))));
  }

  @Test
  public void testReadEmptyApplicationOfConstantWithoutType() {
    Term t = readTerm("f()", null, "");
    assertTrue(t.equals(TermFactory.createConstant("f", type("a -> b -> c -> d"))));
  }

  @Test
  public void testReadEmptyApplicationWithIncorrectType() {
    Term t = readTerm("f()", "b", "1:1: Type error: expected term of " +
      "type b, but got f of type a ⇒ b ⇒ c ⇒ d.\n");
    assertTrue(t.equals(TermFactory.createConstant("f", type("b"))));
  }

  @Test
  public void testReadFullApplication() {
    Term t = readTerm("f(aa,bb,cc)", null, "");
    assertTrue(t.vars().size() == 0);
    assertTrue(t.toString().equals("f(aa, bb, cc)"));
    assertTrue(t.queryType().toString().equals("d"));
  }

  @Test
  public void testReadIncompleteApplication() {
    Term t = CoraInputReader.readTermFromString("f(aa,x)", generateTRS());
    assertTrue(t.vars().size() == 1);
    assertTrue(t.toString().equals("f(aa, x)"));
    assertTrue(t.queryType().toString().equals("c ⇒ d"));
  }

  @Test
  public void testReadApplicationWithTooManyArgsNoTypeGiven() {
    Term t = readTerm("h(aa, bb)", null,
      "1:1: Arity error: h has type (c ⇒ d) ⇒ b, but 2 arguments are given.\n");
    assertTrue(t.vars().size() == 0);
    assertTrue(t.toString().equals("h(aa, bb)"));
    assertTrue(t.queryHead().equals(TermFactory.createConstant("h", type("a ⇒ b ⇒ b"))));
  }

  @Test
  public void testReadApplicationWithTooManyArgsSomeTypeGiven() {
    Term t = readTerm("h(aa, bb)", "x",
      "1:1: Arity error: h has type (c ⇒ d) ⇒ b, but 2 arguments are given.\n");
    assertTrue(t.toString().equals("h(aa, bb)"));
    assertTrue(t.queryHead().equals(TermFactory.createConstant("h", type("a ⇒ b ⇒ x"))));
  }

  @Test
  public void testReadApplicationWithIncorrectOutputType() {
    Term t = readTerm("f(aa,x,cc)", "c",
      "1:1: Type error: expected term of type c, but got f(aa, x, cc) of type d.\n");
    assertTrue(t.toString().equals("f(aa, x, cc)"));
    assertTrue(t.isConstant());
    assertTrue(t.queryType().toString().equals("c"));
  }

  @Test
  public void testReadApplicationWithIncorrectArgumentType() {
    Term t = readTerm("f(x,cc,y)", "d", "1:5: Expected term of type b, " +
      "but got cc, which was declared as a function symbol of type c.\n");
    assertTrue(t.toString().equals("f(x, cc, y)"));
    assertTrue(t.queryHead().equals(TermFactory.createConstant("f", type("a ⇒ b ⇒ c ⇒ d"))));
    assertTrue(t.queryType().toString().equals("d"));
    assertTrue(t.vars().size() == 2);
  }

  @Test
  public void testReadApplicationWithIncorrectArgumentAndOutputType() {
    Term t = readTerm("f(aa,cc,bb)", "c",
      "1:6: Expected term of type b, but got cc, which was declared as a function symbol of type c.\n" +
      "1:9: Expected term of type c, but got bb, which was declared as a function symbol of type b.\n" +
      "1:1: Type error: expected term of type c, but got f(aa, cc, bb) of type d.\n");
    assertTrue(t.toString().equals("f(aa, cc, bb)"));
    assertTrue(t.isConstant());
    assertTrue(t.queryType().toString().equals("c"));
  }

  @Test
  public void testReadApplicationWithInconsistentVariables() {
    Term t = readTerm("f(x, bb, x)", null, "1:10: Expected term of type c, " +
      "but got x, which was previously used as a variable of type a.\n");
    assertTrue(t.toString().equals("f(x__1, bb, x__2)"));
    assertTrue(t.vars().size() == 2);
  }

  @Test
  public void testNestedFunctionalTerm() {
    Term t = readTerm("f(x,h(f(x, bb)),cc)", null, "");
    assertTrue(t.toString().equals("f(x, h(f(x, bb)), cc)"));
    assertTrue(t.queryType().equals(type("d")));
    assertTrue(t.vars().size() == 1);
  }

  @Test
  public void testReadDeclaredVariableApplication() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z( aa,x )", collector);
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("Z", type("a ⇒ b ⇒ a")));
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t.toString().equals("Z(aa, x)"));
    assertTrue(t.queryHead().isVariable());
    assertTrue(data.lookupVariable("x").queryType().equals(type("b")));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testReadUndeclaredVariableApplication() {
    Term t = readTerm("Z(aa)", "b",
    // this is not allowed, even though technically we could derive the type
      "1:1: Undeclared symbol: Z.  Type cannot easily be deduced from context.\n");
    assertTrue(t.toString().equals("Z(aa)"));
    assertTrue(t.queryHead().equals(TermFactory.createConstant("Z", type("a ⇒ b"))));
  }

  @Test
  public void testRepeatedApplication() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("f(aa)(x,cc) next", collector);
    Term t = CoraInputReader.readTermForUnitTest(status, generateSignature(), null);
    assertTrue(t.toString().equals("f(aa, x, cc)"));
    assertTrue(status.nextToken().toString().equals("1:13: next (IDENTIFIER)"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testMissingBracket() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("f(x,h(f(x, bb),cc)", collector);
    assertTrue(CoraInputReader.readTermForUnitTest(status, generateSignature(), null) == null);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:19: Expected a comma or closing bracket ) but got end of input.\n"));
  }

  @Test
  public void testDuplicateComma() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("f(x,,y) next", collector);
    assertTrue(CoraInputReader.readTermForUnitTest(status, generateSignature(), null) == null);
    assertTrue(status.nextToken().toString().equals("1:9: next (IDENTIFIER)"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:5: Unexpected comma; expected term or closing bracket )\n"));
  }

  @Test
  public void testOnlyCommas() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("f(,,,) next", collector);
    assertTrue(CoraInputReader.readTermForUnitTest(status, generateSignature(), null) == null);
    assertTrue(status.nextToken().toString().equals("1:8: next (IDENTIFIER)"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:3: Unexpected comma; expected term or closing bracket )\n" +
      "1:6: Expected term, started by an identifier, λ, string or (, but got BRACKETCLOSE ()).\n"));
  }

  @Test
  public void testMissingComma() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("f(x,h(f(x, bb)) cc) next", collector);
    assertTrue(CoraInputReader.readTermForUnitTest(status, generateSignature(), null) == null);
    assertTrue(status.nextToken().toString().equals("1:21: next (IDENTIFIER)"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:17: Expected a comma or closing bracket ) but got IDENTIFIER (cc).\n"));
  }

  @Test
  public void testReadBasicAbstraction() {
    Term t = readTerm("λx :: a. f(x, bb, y)", null, "");
    assertTrue(t.toString().equals("λx.f(x, bb, y)"));
    assertTrue(t.vars().size() == 1);
    assertTrue(t.queryType().toString().equals("a ⇒ d"));
  }

  @Test
  public void testReadMultipleAbstractionWithBinderDeclarations() {
    Term t = readTerm("λx :: a, y ::c. f(x, bb, y)", null, "");
    assertTrue(t.toString().equals("λx.λy.f(x, bb, y)"));
    assertTrue(t.vars().size() == 0);
    assertTrue(t.queryType().toString().equals("a ⇒ c ⇒ d"));
  }

  @Test
  public void testReadAbstractionWithoutBinderDeclaration() {
    Term t = readTerm("h(\\x.f(aa,bb,x))", null, "");
    assertTrue(t.toString().equals("h(λx.f(aa, bb, x))"));
    assertTrue(t.vars().size() == 0);
  }

  @Test
  public void testReadAbstractionWithTypeExpectationGivenButUnnecessary() {
    Term t = readTerm("\\x::a.f(x,bb, cc)", "a -> d", "");
    assertTrue(t.toString().equals("λx.f(x, bb, cc)"));
    assertTrue(t.vars().size() == 0);
    assertTrue(t.queryType().toString().equals("a ⇒ d"));
  }

  @Test
  public void testReadAbstractionWithTypeExpectationGivenAndNecessary() {
    Term t = readTerm("λx.f(x,bb, cc)", "a -> d", "");
    assertTrue(t.toString().equals("λx.f(x, bb, cc)"));
    assertTrue(t.vars().size() == 0);
    assertTrue(t.queryType().toString().equals("a ⇒ d"));
  }

  @Test
  public void testReadAbstractionWithTypeExpectationGivenThatDoesNotMatchInput() {
    Term t = readTerm("\\x::a.f(x,bb, cc)", "b -> d",
      "1:2: Type error: expected subterm of type b ⇒ d, but got abstraction with variable of type a.\n" +
      "1:9: Expected term of type a, but got x, which was previously used as a variable of type b.\n");
    assertTrue(t.toString().equals("λx1.f(x, bb, cc)"));
    assertTrue(t.vars().size() == 1);
    assertTrue(t.queryType().toString().equals("b ⇒ d"));
  }

  @Test
  public void testReadAbstractionWithTypeExpectationGivenThatDoesNotMatchOutput() {
    Term t = readTerm("\\x::a.f(x,bb, cc)", "a -> c",
      "1:7: Type error: expected term of type c, but got f(x, bb, cc) of type d.\n");
    assertTrue(t.toString().equals("λx.f(x, bb, cc)"));
    assertTrue(t.vars().size() == 0);
    assertTrue(t.queryType().toString().equals("a ⇒ c"));
  }

  @Test
  public void testReadAbstractionWhereTypeCannotFullyBeDerived() {
    Term t = readTerm("\\x :: a, y, z :: c.f(x,y,z)", null,
      "1:10: Cannot derive type of binder y from context; it should be denoted directly in the "+
        "abstraction.\n");
    assertTrue(t.toString().equals("λx.λy1.λz.f(x, y, z)"));
    assertTrue(t.vars().size() == 1);
    assertTrue(t.queryType().toString().equals("a ⇒ o ⇒ c ⇒ d"));
  }

  @Test
  public void testReadAbstractionTypeOfVariableGivenInTheWrongWay() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("λx.x", collector);
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("x", type("a")));
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t.toString().equals("λx1.x"));
    assertTrue(t.queryType().toString().equals("o ⇒ a"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:2: Cannot derive type of binder x from context; it should be denoted directly " +
      "in the abstraction.\n"));
  }

  @Test
  public void testReadAbstractionWhenParseDataAlreadyContainsVariableAsBinder() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("λx::b.x", collector);
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createBinder("x", type("a")));
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t.toString().equals("λx.x"));
    assertTrue(t.queryType().toString().equals("b ⇒ b"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("a"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testReadAbstractionWhenParseDataAlreadyContainsVariableAsFree() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("λx::b.x", collector);
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("x", type("a")));
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t.toString().equals("λx.x"));
    assertTrue(t.queryType().toString().equals("b ⇒ b"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("a"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:2: Ambiguous binder: this name has already been declared as a free variable.\n"));
  }

  @Test
  public void testReadAbstractionWhenParseDataAlreadyContainsVariableAsFunction() {
    Term t = readTerm("λaa::b.aa", null,
      "1:2: Ambiguous binder: this name has already been declared as a function symbol.\n");
    assertTrue(t.toString().equals("λaa.aa"));
    assertTrue(t.queryType().toString().equals("b ⇒ a"));
  }

  @Test
  public void testReadAbstractionWhenParseDataAlreadyContainsVariableAsMetavariable() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("λx::a.x[ x ]", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("x", type("a -> b"), 1));
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t.toString().equals("λx1.x⟨x1⟩"));
    assertTrue(t.queryType().toString().equals("a ⇒ b"));
    assertTrue(data.lookupMetaVariable("x").queryType().toString().equals("a ⇒ b"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:2: Ambiguous binder: this name has already been declared as a meta-variable.\n"));
  }

  @Test
  public void testReadAbstractionWithDuplicateVariableName() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("λx::a, y :: b, x :: c.x", collector);
    SymbolData data = generateSignature();
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t.toString().equals("λx.λy.λx1.x1"));
    assertTrue(t.queryType().toString().equals("a ⇒ b ⇒ c ⇒ c"));
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(data.lookupVariable("x") == null);
  }

  @Test
  public void testReadAbstractionAtHeadOfApplication() {
    Term t = readTerm("(λx :: a, y ::c. f(x,bb,y))(aa,cc)", null, "");
    assertTrue(t.toString().equals("(λx.λy.f(x, bb, y))(aa, cc)"));
    assertTrue(t.queryType().toString().equals("d"));
  }

  @Test
  public void testReadAbstractionWithBrokenType() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("λx :: a -> .x y", collector);
    Term t = CoraInputReader.readTermForUnitTest(status, generateSignature(), null);
    assertTrue(t.toString().equals("λx.x"));
    assertTrue(t.queryType().toString().equals("a ⇒ a"));
    assertTrue(status.nextToken().toString().equals("1:15: y (IDENTIFIER)"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:12: Expected a type (started by a constant or bracket) but got DOT (.).\n"));
  }

  @Test
  public void testReadAbstractionWithMissingType() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("λx :: .x y", collector);
    Term t = CoraInputReader.readTermForUnitTest(status, generateSignature(), type("o ⇒ o"));
    assertTrue(t == null);
    assertTrue(status.nextToken().toString().equals("1:10: y (IDENTIFIER)"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:7: Expected a type (started by a constant or bracket) but got DOT (.).\n"));
  }

  @Test
  public void testReadMultipleAbstractionWithMissingComma() {
    Term t = readTerm("\\x :: a y.f(x,y,cc)", "a -> b -> d",
      "1:9: Expected a comma or dot but got IDENTIFIER (y).\n");
    assertTrue(t.toString().equals("λx.λy.f(x, y, cc)"));
    assertTrue(t.queryType().toString().equals("a ⇒ b ⇒ d"));
  }

  @Test
  public void testCompletelyDifferentTokenInAbstractionList() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("\\x \"test\".aa", collector);
    assertTrue(CoraInputReader.readTermForUnitTest(status, generateSignature(), null) == null);
    assertTrue(status.nextToken().toString().equals("1:10: . (DOT)"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:4: Expected a comma or dot but got STRING (\"test\").\n"));
  }

  @Test
  public void testMissingBinderName() {
    Term t = readTerm("λ :: a, x :: b.x", null,
      "1:3: Expected an identifier (variable name) but got DECLARE (::).\n");
    assertTrue(t == null);
  }

  @Test
  public void testExtraCommaInAbstractionBinders() {
    Term t = readTerm("λ x, .aa", null,
      "1:6: Expected an identifier (variable name) but got DOT (.).\n");
    assertTrue(t == null);
  }

  @Test
  public void testUndeclaredMetaVariableWithEmptyArgumentsListTypeGiven() {
    Term t = readTerm("Z[]", "a ⇒ b", "");
    assertTrue(t.isVariable());
    assertTrue(t.queryType().equals(type("a ⇒ b")));
    assertTrue(t.toString().equals("Z"));
  }

  @Test
  public void testUndeclaredMetaVariableWithEmptyArgumentsListTypeNotGiven() {
    Term t = readTerm("Z⟨⟩", null,
      "1:1: Undeclared (meta-)variable: Z.  Type cannot easily be deduced from context.\n");
    assertTrue(t.isVariable());
    assertTrue(t.queryType().toString().equals("o"));
    assertTrue(t.toString().equals("Z"));
  }

  @Test
  public void testDeclaredMetaVariableWithEmptyArgumentsListCorrectTypeGiven() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z[⟩", collector);
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("Z", type("b")));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("b"));
    assertTrue(t.isVariable());
    assertTrue(t.toString().equals("Z"));
    assertTrue(t.queryType().equals(type("b")));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testDeclaredMetaVariableWithEmptyArgumentsListIncorrectTypeGiven() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z⟨⟩", collector);
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("Z", type("b ⇒ a")));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("a ⇒ b"));
    assertTrue(t.isVariable());
    assertTrue(t.toString().equals("Z"));
    assertTrue(t.queryType().equals(type("a ⇒ b")));
    assertTrue(data.lookupVariable("Z").queryType().equals(type("b ⇒ a")));
    assertTrue(collector.queryCollectedMessages().equals("1:1: Expected term of type a ⇒ b, " +
      "but got Z, which was previously used as a variable of type b ⇒ a.\n"));
  }

  @Test
  public void testDeclaredMetaVariableWithEmptyArgumentsListTypeNotGiven() {
    // declared as higher type
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z⟨]", collector);
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("Z", type("b ⇒ a")));
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t.isVariable());
    assertTrue(t.toString().equals("Z"));
    assertTrue(t.queryType().equals(type("b ⇒ a")));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testMetaVariableWithEmptyArgumentsListDeclaredAsFunctionSymbol() {
    Term t = readTerm("aa[]", null, "1:1: Meta-application for meta-variable aa, " +
      "which was previously declared as a function symbol.\n");
    assertTrue(t.toString().equals("aa"));
    assertTrue(t.isVariable());
    assertTrue(t.queryType().toString().equals("a"));
  }

  @Test
  public void testMetaVariableWithEmptyArgumentsListDeclaredAsBinder() {
    // declared as higher type
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z[]", collector);
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createBinder("Z", type("b ⇒ a")));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("x"));
    assertTrue(t.isVariable());
    assertTrue(t.toString().equals("Z"));
    assertTrue(t.queryType().equals(type("x")));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:1: Binder variable Z used as meta-variable.\n"));
  }

  @Test
  public void testMetaVariableWithEmptyArgumentsListDeclaredAsHigherMetaVar() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z⟨⟩", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("b ⇒ a"), 1));
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t.isVariable());
    assertTrue(t.toString().equals("Z"));
    assertTrue(t.queryType().equals(type("b ⇒ a")));
    assertTrue(collector.queryCollectedMessages().equals("1:1: Meta-application for " +
      "meta-variable Z has no arguments, when it previously occurred (or was declared) " +
      "with arity 1\n"));
  }

  @Test
  public void testMetaApplicationWithUndeclaredMetaButDeclaredArgsTypeKnown() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z[x]", collector);
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createBinder("x", type("a")));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("b -> c"));
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x⟩"));
    assertTrue(t.queryType().toString().equals("b ⇒ c"));
    MetaVariable z = data.lookupMetaVariable("Z");
    assertTrue(z.queryArity() == 1);
    assertTrue(z.queryType().toString().equals("a ⇒ b ⇒ c"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testMetaApplicationWithUndeclaredMetaButDeclaredArgsTypeUnknown() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z[x]", collector);
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createBinder("x", type("a")));
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x⟩"));
    assertTrue(t.queryType().toString().equals("o"));
    assertTrue(data.lookupMetaVariable("Z") == null);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:1: Cannot derive output type of meta-variable Z from context.\n"));
  }

  @Test
  public void testMetaApplicationWithDeclaredMetaButUndeclaredArg() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z[x]", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a ⇒ a"), 1));
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x⟩"));
    assertTrue(t.queryType().toString().equals("a"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("a"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testMetaApplicationWithEverythingDeclaredButIncorrectType() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z[x⟩", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a ⇒ a"), 1));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("b"));
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x⟩"));
    assertTrue(t.queryType().toString().equals("b"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("a"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:1: Meta-variable Z has output type a while a term of type b was expected.\n"));
  }

  @Test
  public void testMetaApplicationWithNothingDeclared() {
    Term t = readTerm("Z[x,aa,y]", null,
      "1:1: Cannot derive output type of meta-variable Z from context.\n" +
      "1:3: Undeclared symbol: x.  Type cannot easily be deduced from context.\n" +
      "1:8: Undeclared symbol: y.  Type cannot easily be deduced from context.\n");
    assertTrue(t.toString().equals("Z⟨x, aa, y⟩"));
    assertTrue(t.queryType().toString().equals("o"));
  }

  @Test
  public void testMetaApplicationWithJustOnePartMissing() {
    Term t = readTerm("Z[x,aa]", "u",
      "1:3: Undeclared symbol: x.  Type cannot easily be deduced from context.\n");
    assertTrue(t.toString().equals("Z⟨x, aa⟩"));
    assertTrue(t.queryType().toString().equals("u"));
  }

  @Test
  public void testMetaVariableAlreadyDeclaredAsFunctionSymbolWithTypeExpected() {
    Term t = readTerm("f⟨aa,y]", "c ⇒ e",
      "1:1: Unexpected meta-application with meta-variable f, which was previously declared as a function symbol.\n" +
      "1:6: Undeclared symbol: y.  Type cannot easily be deduced from context.\n");
    assertTrue(t.queryType().toString().equals("c ⇒ e"));
    assertTrue(t.toString().equals("f⟨aa, y⟩"));
  }

  @Test
  public void testMetaVariableAlreadyDeclaredAsFunctionSymbolWithoutTypeExpected() {
    Term t = readTerm("f⟨aa⟩", null, "1:1: Unexpected meta-application with meta-variable " +
      "f, which was previously declared as a function symbol.\n");
    assertTrue(t.queryType().toString().equals("o"));
    assertTrue(t.toString().equals("f⟨aa⟩"));
  }

  @Test
  public void testMetaVariableAlreadyDeclaredAsVariable() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z[x]", collector);
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("Z", type("a ⇒ a")));
    data.addVariable(TermFactory.createVar("x", type("b")));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("b"));
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x⟩"));
    assertTrue(t.queryType().toString().equals("b"));
    assertTrue(data.lookupVariable("Z").queryType().toString().equals("a ⇒ a"));
    assertTrue(data.lookupMetaVariable("Z").queryType().toString().equals("b ⇒ b"));
    assertTrue(collector.queryCollectedMessages().equals("1:1: Unexpected " +
      "meta-application with meta-variable Z, which was previously used (or declared) " +
      "as a variable without meta-arguments.\n"));
  }

  @Test
  public void testMetaVariableDeclaredWithGreaterArity() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z[x]", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a ⇒ a ⇒ a"), 2));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("zot"));
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x⟩"));
    assertTrue(t.queryType().toString().equals("zot"));
    assertTrue(data.lookupVariable("x") == null);
    assertTrue(t.queryMetaVariable().queryType().toString().equals("o ⇒ zot"));
    assertTrue(collector.queryCollectedMessages().equals("1:1: Meta-variable Z was " +
      "previously used (or declared) with arity 2, but is here used with 1 arguments.\n"));
  }

  @Test
  public void testMetaVariableDeclaredWithSmallerArity() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z⟨aa,y⟩", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a ⇒ a ⇒ a"), 1));
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨aa, y⟩"));
    assertTrue(t.queryType().toString().equals("a ⇒ a"));
    assertTrue(t.queryMetaVariable().queryType().toString().equals("a ⇒ o ⇒ a ⇒ a"));
    assertTrue(collector.queryCollectedMessages().equals("1:1: Meta-variable Z was " +
      "previously used (or declared) with arity 1, but is here used with 2 arguments.\n"));
  }

  @Test
  public void testCorrectMultiApplicationWithMetaVariableDeclared() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z⟨x,y⟩", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a ⇒ a ⇒ a"), 2));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("a"));
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x, y⟩"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("a"));
    assertTrue(data.lookupVariable("y").queryType().toString().equals("a"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testReadNestedMeta() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z⟨aa,Y[x⟩,cc]", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Y", type("a ⇒ b"), 1));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("d"));
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨aa, Y⟨x⟩, cc⟩"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("a"));
    assertTrue(data.lookupMetaVariable("Z").queryType().toString().equals("a ⇒ b ⇒ c ⇒ d"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testAppliedMetaApplication() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z⟨aa⟩(bb,cc)", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a ⇒ b ⇒ c ⇒ d"), 1));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("d"));
    assertFalse(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨aa⟩(bb, cc)"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testMetaApplicationWithExtraComma() {
    Term t = readTerm("Z[aa,,bb]", "u",
      "1:6: Unexpected comma; expected term or meta-closing bracket ]\n");
    assertTrue(t == null);
  }

  @Test
  public void testMetaApplicationWithMissingCommas() {
    Term t = readTerm("Z[aa bb cc]", "u",
      "1:6: Expected a comma or meta-closing bracket ] but got IDENTIFIER (bb).\n" +
      "1:9: Expected a comma or meta-closing bracket ] but got IDENTIFIER (cc).\n");
    assertTrue(t == null);
  }

  @Test
  public void testMissingCloseBracket() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("Z⟨aa,x}", collector);
    Term t = CoraInputReader.readTermForUnitTest(status, generateSignature(), type("d"));
    assertTrue(t == null);
    assertTrue(status.nextToken().toString().equals("1:7: } (BRACECLOSE)"));
    assertTrue(collector.queryCollectedMessages().equals("1:7: Expected a comma or " +
      "meta-closing bracket ⟩ but got BRACECLOSE (}).\n"));
  }
}

