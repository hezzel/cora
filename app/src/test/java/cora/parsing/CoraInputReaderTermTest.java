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
  private ParsingStatus makeUStatus(String text, ErrorCollector collector) {
    return new ParsingStatus(CoraTokenData.getUnconstrainedStringLexer(text), collector);
  }

  private ParsingStatus makeCStatus(String text, ErrorCollector collector) {
    return new ParsingStatus(CoraTokenData.getConstrainedStringLexer(text), collector);
  }

  private Type type(String str) {
    return CoraInputReader.readTypeFromString(str);
  }

  private SymbolData generateSignature() {
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(TermFactory.createConstant("f", type("a → b → c → d")));
    data.addFunctionSymbol(TermFactory.createConstant("aa", type("a")));
    data.addFunctionSymbol(TermFactory.createConstant("bb", type("b")));
    data.addFunctionSymbol(TermFactory.createConstant("cc", type("c")));
    data.addFunctionSymbol(TermFactory.createConstant("h", type("(c → d) → b")));
    return data;
  }

  private TRS generateTRS(boolean constrained) {
    if (constrained) return TRSFactory.createCoraTRS(generateSignature().queryCurrentAlphabet(),
                                                     new ArrayList<Rule>(), false);
    else return TRSFactory.createAMS(generateSignature().queryCurrentAlphabet(),
                                     new ArrayList<Rule>(), false);
  }

  private Term readTerm(String txt, String expected, boolean constrained, String message) {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = constrained ? makeCStatus(txt + " NEXT", collector)
                                       : makeUStatus(txt + " NEXT", collector);
    Type type = expected == null ? null : CoraInputReader.readTypeFromString(expected);
    Term t = CoraInputReader.readTermForUnitTest(status, generateSignature(), type);
    assertTrue(status.nextToken().getText().equals("NEXT"));
    assertTrue(collector.queryCollectedMessages().equals(message));
    return t;
  }

  private Term readTermPrint(String txt, String expected, boolean constrained, String message) {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = constrained ? makeCStatus(txt + " NEXT", collector)
                                       : makeUStatus(txt + " NEXT", collector);
    Type type = expected == null ? null : CoraInputReader.readTypeFromString(expected);
    Term t = CoraInputReader.readTermForUnitTest(status, generateSignature(), type);
    System.out.println("t = " + t);
    System.out.println(collector.queryCollectedMessages());
    assertTrue(false);
    return null;
  }

  @Test
  public void testReadSingleString() {
    Term term = CoraInputReader.readTermFromString("\"hello world!\\n\"", generateTRS(true));
    assertTrue(term.queryType().toString().equals("String"));
    assertTrue(term.toString().equals("\"hello world!\\n\""));
  }

  @Test
  public void testUndeclaredMetaVariableWithEmptyArgumentsListTypeGiven() {
    Term t = readTerm("Z[]", "a → b", false, "");
    assertTrue(t.isVariable());
    assertTrue(t.queryType().equals(type("a → b")));
    assertTrue(t.toString().equals("Z"));
  }

  @Test
  public void testUndeclaredMetaVariableWithEmptyArgumentsListTypeNotGiven() {
    Term t = readTerm("Z⟨⟩", null, true,
      "1:1: Undeclared (meta-)variable: Z.  Type cannot easily be deduced from context.\n");
    assertTrue(t.isVariable());
    assertTrue(t.queryType().toString().equals("o"));
    assertTrue(t.toString().equals("Z"));
  }

  @Test
  public void testDeclaredMetaVariableWithEmptyArgumentsListCorrectTypeGiven() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeUStatus("Z[⟩", collector);
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
    ParsingStatus status = makeCStatus("Z⟨⟩", collector);
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("Z", type("b → a")));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("a → b"));
    assertTrue(t.isVariable());
    assertTrue(t.toString().equals("Z"));
    assertTrue(t.queryType().equals(type("a → b")));
    assertTrue(data.lookupVariable("Z").queryType().equals(type("b → a")));
    assertTrue(collector.queryCollectedMessages().equals("1:1: Expected term of type a → b, " +
      "but got Z, which was previously used as a variable of type b → a.\n"));
  }

  @Test
  public void testDeclaredMetaVariableWithEmptyArgumentsListTypeNotGiven() {
    // declared as higher type
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeCStatus("Z⟨]", collector);
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("Z", type("b → a")));
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t.isVariable());
    assertTrue(t.toString().equals("Z"));
    assertTrue(t.queryType().equals(type("b → a")));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testMetaVariableWithEmptyArgumentsListDeclaredAsFunctionSymbol() {
    Term t = readTerm("aa[]", null, false, "1:1: Meta-application for meta-variable aa, " +
      "which was previously declared as a function symbol.\n");
    assertTrue(t.toString().equals("aa"));
    assertTrue(t.isVariable());
    assertTrue(t.queryType().toString().equals("a"));
  }

  @Test
  public void testMetaVariableWithEmptyArgumentsListDeclaredAsBinder() {
    // declared as higher type
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeCStatus("Z[]", collector);
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createBinder("Z", type("b → a")));
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
    ParsingStatus status = makeUStatus("Z⟨⟩", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("b → a"), 1));
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t.isVariable());
    assertTrue(t.toString().equals("Z"));
    assertTrue(t.queryType().equals(type("b → a")));
    assertTrue(collector.queryCollectedMessages().equals("1:1: Meta-application for " +
      "meta-variable Z has no arguments, when it previously occurred (or was declared) " +
      "with arity 1\n"));
  }

  @Test
  public void testMetaApplicationWithUndeclaredMetaButDeclaredArgsTypeKnown() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeUStatus("Z[x]", collector);
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createBinder("x", type("a")));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("b -> c"));
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x⟩"));
    assertTrue(t.queryType().toString().equals("b → c"));
    MetaVariable z = data.lookupMetaVariable("Z");
    assertTrue(z.queryArity() == 1);
    assertTrue(z.queryType().toString().equals("a → b → c"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testMetaApplicationWithUndeclaredMetaButDeclaredArgsTypeUnknown() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeUStatus("Z[x]", collector);
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
    ParsingStatus status = makeCStatus("Z[x]", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a → a"), 1));
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
    ParsingStatus status = makeCStatus("Z[x⟩", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a → a"), 1));
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
    Term t = readTerm("Z[x,aa,y]", null, false,
      "1:1: Cannot derive output type of meta-variable Z from context.\n" +
      "1:3: Undeclared symbol: x.  Type cannot easily be deduced from context.\n" +
      "1:8: Undeclared symbol: y.  Type cannot easily be deduced from context.\n");
    assertTrue(t.toString().equals("Z⟨x, aa, y⟩"));
    assertTrue(t.queryType().toString().equals("o"));
  }

  @Test
  public void testMetaApplicationWithJustOnePartMissing() {
    Term t = readTerm("Z[x,aa]", "u", true,
      "1:3: Undeclared symbol: x.  Type cannot easily be deduced from context.\n");
    assertTrue(t.toString().equals("Z⟨x, aa⟩"));
    assertTrue(t.queryType().toString().equals("u"));
  }

  @Test
  public void testMetaVariableAlreadyDeclaredAsFunctionSymbolWithTypeExpected() {
    Term t = readTerm("f⟨aa,y]", "c → e", true,
      "1:1: Unexpected meta-application with meta-variable f, which was previously declared as a function symbol.\n" +
      "1:6: Undeclared symbol: y.  Type cannot easily be deduced from context.\n");
    assertTrue(t.queryType().toString().equals("c → e"));
    assertTrue(t.toString().equals("f⟨aa, y⟩"));
  }

  @Test
  public void testMetaVariableAlreadyDeclaredAsFunctionSymbolWithoutTypeExpected() {
    Term t = readTerm("f⟨aa⟩", null, false, "1:1: Unexpected meta-application with " +
      "meta-variable f, which was previously declared as a function symbol.\n");
    assertTrue(t.queryType().toString().equals("o"));
    assertTrue(t.toString().equals("f⟨aa⟩"));
  }

  @Test
  public void testMetaVariableAlreadyDeclaredAsVariable() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeUStatus("Z[x]", collector);
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("Z", type("a → a")));
    data.addVariable(TermFactory.createVar("x", type("b")));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("b"));
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x⟩"));
    assertTrue(t.queryType().toString().equals("b"));
    assertTrue(data.lookupVariable("Z").queryType().toString().equals("a → a"));
    assertTrue(data.lookupMetaVariable("Z").queryType().toString().equals("b → b"));
    assertTrue(collector.queryCollectedMessages().equals("1:1: Unexpected " +
      "meta-application with meta-variable Z, which was previously used (or declared) " +
      "as a variable without meta-arguments.\n"));
  }

  @Test
  public void testMetaVariableDeclaredWithGreaterArity() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeUStatus("Z[x]", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a → a → a"), 2));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("zot"));
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x⟩"));
    assertTrue(t.queryType().toString().equals("zot"));
    assertTrue(data.lookupVariable("x") == null);
    assertTrue(t.queryMetaVariable().queryType().toString().equals("o → zot"));
    assertTrue(collector.queryCollectedMessages().equals("1:1: Meta-variable Z was " +
      "previously used (or declared) with arity 2, but is here used with 1 arguments.\n"));
  }

  @Test
  public void testMetaVariableDeclaredWithSmallerArity() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeCStatus("Z⟨aa,y⟩", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a → a → a"), 1));
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨aa, y⟩"));
    assertTrue(t.queryType().toString().equals("a → a"));
    assertTrue(t.queryMetaVariable().queryType().toString().equals("a → o → a → a"));
    assertTrue(collector.queryCollectedMessages().equals("1:1: Meta-variable Z was " +
      "previously used (or declared) with arity 1, but is here used with 2 arguments.\n"));
  }

  @Test
  public void testCorrectMultiApplicationWithMetaVariableDeclared() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeUStatus("Z⟨x,y⟩", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a → a → a"), 2));
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
    ParsingStatus status = makeCStatus("Z⟨aa,Y[x⟩,cc]", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Y", type("a → b"), 1));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("d"));
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨aa, Y⟨x⟩, cc⟩"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("a"));
    assertTrue(data.lookupMetaVariable("Z").queryType().toString().equals("a → b → c → d"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testAppliedMetaApplication() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeCStatus("Z⟨aa⟩(bb,cc)", collector);
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a → b → c → d"), 1));
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("d"));
    assertFalse(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨aa⟩(bb, cc)"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testReadSimpleNot() {
    Term t = readTerm("¬x", null, true, "");
    assertTrue(t.isFunctionalTerm());
    assertTrue(t.queryRoot().isTheorySymbol());
    assertTrue(t.vars().size() == 1);
    assertTrue(t.toString().equals("¬x"));
  }

  @Test
  public void testMostlySimpleMinus() {
    Term t = readTerm("- (3+x)", null, true, "");
    assertTrue(t.toString().equals("-(3 + x)"));
    assertTrue(t.queryType().toString().equals("Int"));
  }

  @Test
  public void testDuplicateNot() {
    Term t = readTerm("¬¬ ( x > 0)", null, true, "");
    assertTrue(t.toString().equals("¬(¬(x > 0))"));
  }

  @Test
  public void testBadBracketOmission() {
    Term t = readTerm("¬ x > 0", "Bool", true,
      "1:1: Type error: expected term of type Int, but got ¬x of type Bool.\n");
    assertTrue(t.toString().equals("¬x > 0"));
  }

  @Test
  public void testReadSimpleInfix() {
    Term t = readTerm("1+2", null, true, "");
    assertTrue(t.toString().equals("1 + 2"));
    assertTrue(t.queryType().toString().equals("Int"));
  }

  @Test
  public void testReadInfixWithLeftToRightPriority() {
    Term t = readTerm("1*2+3  > x", null, true, "");
    assertTrue(t.toString().equals("1 * 2 + 3 > x"));
    assertTrue(t.vars().size() == 1);
    assertTrue(t.queryType().toString().equals("Bool"));
  }

  @Test
  public void testReadInfixWithRightToLeftPriority() {
    Term t = readTerm("x >= 3 + y * 2", null, true, "");
    assertTrue(t.toString().equals("x ≥ 3 + y * 2"));
    assertTrue(t.vars().size() == 2);
    assertTrue(t.queryType().toString().equals("Bool"));
  }

  @Test
  public void testReadNegativeInteger() {
    Term t = readTerm("-  5", null, true, "");
    assertTrue(t.equals(TheoryFactory.createValue(-5)));
  }

  @Test
  public void testMinusBeforeAddition() {
    Term t = readTerm("- x + y", null, true, "");
    assertTrue(t.toString().equals("-x + y"));
    assertTrue(t.queryRoot().toString().equals("+"));
    assertTrue(t.queryArgument(1).queryRoot().toString().equals("-"));
  }

  @Test
  public void testNegativeIntegerInMultiplication() {
    Term t = readTerm("-2*1", null, true, "");
    assertTrue(t.toString().equals("-2 * 1"));
    assertTrue(t.queryRoot().toString().equals("*"));
    assertTrue(t.queryArgument(1).queryRoot().toString().equals("-2"));
  }

  @Test
  public void testReadSimpleMinusWithNegation() {
    Term t = readTerm("x - y", null, true, "");
    // this becomes: x + -y
    assertTrue(t.toString().equals("x - y"));
    assertTrue(t.queryRoot().toString().equals("+"));
    assertTrue(t.queryArgument(2).queryRoot().toString().equals("-"));
  }

  @Test
  public void testReadSimpleMinusWithConstant() {
    Term t = readTerm("x - 3", null, true, "");
    assertTrue(t.toString().equals("x - 3"));
    assertTrue(t.queryRoot().toString().equals("+"));
    assertTrue(t.queryArgument(2).queryRoot().toString().equals("-3"));
  }

  @Test
  public void testReadComplexMinuses() {
    Term t = readTerm("x -3 * 5 + 1 < -1-y", null, true, "");
    assertTrue(t.toString().equals("x - 3 * 5 + 1 < -1 - y"));
    assertTrue(t.vars().size() == 2);
    assertTrue(t.queryArgument(1).queryArgument(1).toString().equals("x - 3 * 5"));
    assertTrue(t.queryArgument(1).queryArgument(1).queryArgument(2).toString().equals("-(3 * 5)"));
  }

  @Test
  public void testMixedInfixPriorities() {
    ErrorCollector collector = new ErrorCollector(10);
    SymbolData data = generateSignature();
    data.addFunctionSymbol(TermFactory.createConstant("q", type("b → Int")));
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a → Int"), 1));
    ParsingStatus status = makeCStatus("q(x) < y /\\ y > Z[aa] + -13 * z +9", collector);
    Term t = CoraInputReader.readTermForUnitTest(status, data, type("Bool"));
    assertTrue(t.isFunctionalTerm());
    assertFalse(t.isTheoryTerm());
    assertTrue(t.toString().equals("q(x) < y ∧ y > Z⟨aa⟩ + -13 * z + 9"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("b"));
    assertTrue(data.lookupVariable("z").queryType().toString().equals("Int"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testDoublePlus() {
    ErrorCollector collector = new ErrorCollector(10);
    SymbolData data = generateSignature();
    ParsingStatus status = makeCStatus("1 ++2", collector);
    Term t = CoraInputReader.readTermForUnitTest(status, data, null);
    assertTrue(t == null);
    assertTrue(status.nextToken().toString().equals("1:4: + (PLUS)"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:4: Expected term, started by an identifier, λ, string or (, but got PLUS (+).\n"));
  }

  @Test
  public void testReadInfixMinus() {
    Term t = readTerm("[-]", null, true, "");
    assertTrue(t.equals(TheoryFactory.minusSymbol));
    t = readTerm("[-](3)", null, true, "");
    assertTrue(t.toString().equals("-3"));
    assertTrue(t.isApplication());
    t = readTerm("[-](3, 4)", null, true,
      "1:2: Arity error: - has type Int → Int, but 2 arguments are given.\n");
  }

  @Test
  public void testReadInfixPlus() {
    Term t = readTerm("[+]", null, true, "");
    assertTrue(t.equals(TheoryFactory.plusSymbol));
    t = readTerm("[+](3)", null, true, "");
    assertTrue(t.toString().equals("+(3)"));
    t = readTerm("[+](3, 4)", null, true, "");
    assertTrue(t.toString().equals("3 + 4"));
  }
}

