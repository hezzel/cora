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
import cora.terms.Variable;
import cora.terms.FunctionSymbol;
import cora.terms.TermFactory;
import cora.rewriting.Rule;
import cora.rewriting.TRS;
import cora.parsing.lib.ErrorCollector;
import cora.parsing.lib.ParsingStatus;

public class TrsInputReaderTest {
  private ParsingStatus makeStatus(String text) {
    return new ParsingStatus(TrsTokenData.getStringLexer(text), 10);
  }

  private ParsingStatus makeStatus(String text, ErrorCollector collector) {
    return new ParsingStatus(TrsTokenData.getStringLexer(text), collector);
  }

  // ====================================== reading a varlist =====================================

  @Test
  public void testReadCorrectVarList() {
    ParsingStatus status = makeStatus("(VAR x y) blaat");
    SymbolData data = TrsInputReader.readVariableDeclaration(status);
    assertTrue(data != null);
    status.throwCollectedErrors();    // this shouldn't throw any errors

    assertTrue(data.lookupVariable("x") != null);
    assertTrue(data.lookupVariable("y") != null);
    assertTrue(data.lookupVariable("z") == null);
    assertTrue(data.lookupVariable("x").queryType().toString().equals("o"));

    assertTrue(status.nextToken().getText().equals("blaat"));
  }

  @Test
  public void testReadVarListWithIllegalTokens() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("(VAR x -> y ( 23) ==", collector);
    try { TrsInputReader.readVariableDeclaration(status); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
      "1:8: Unexpected token: -> (ARROW); expected a variable name\n"));
    }
  }

  @Test
  public void testReadVarListWithDoubleDeclaration() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("(VAR x y x 12 y)", collector);
    SymbolData data = TrsInputReader.readVariableDeclaration(status);

    assertTrue(data.lookupVariable("x") != null);
    assertTrue(data.lookupVariable("y") != null);
    assertTrue(data.lookupVariable("12") != null);

    assertTrue(status.nextToken().isEof());

    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:10: Double declaration of variable x\n" +
      "1:15: Double declaration of variable y\n"));
  }

  @Test
  public void testReadVarListThatDoesNotEnd() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("  (VAR x y 12 ", collector);
    SymbolData data = TrsInputReader.readVariableDeclaration(status);

    assertTrue(data.lookupVariable("x") != null);
    assertTrue(data.lookupVariable("y") != null);
    assertTrue(data.lookupVariable("12") != null);

    assertTrue(status.nextToken().isEof());

    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:3: Encountered end of input while reading varlist; no closing bracket given.\n"));

  }

  @Test
  public void testReadVarListWithRuleListInTheMiddle() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("  (VAR x y 12 (RULES ))", collector);
    SymbolData data = TrsInputReader.readVariableDeclaration(status);

    assertTrue(data.lookupVariable("x") != null);
    assertTrue(data.lookupVariable("y") != null);
    assertTrue(data.lookupVariable("12") != null);

    assertTrue(status.nextToken().getName().equals("RULESDECSTART"));

    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:15: Unexpected (RULES while reading varlist; did you forget a closing bracket?\n"));
  }

  @Test
  public void testReadVarListWithMultipleProblems() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("  (VAR x \ny x ( 12 -> y y (RULES ))", collector);

    try {
      TrsInputReader.readVariableDeclaration(status);
    }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "2:3: Double declaration of variable x\n" +
        "2:5: Unexpected token: ( (BRACKETOPEN); expected a variable name\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadNonVarList() {
    ParsingStatus status = makeStatus("(SIG x y) blaat");
    SymbolData data = TrsInputReader.readVariableDeclaration(status);
    assertTrue(data == null);
    status.throwCollectedErrors();    // this shouldn't throw any errors

    assertTrue(status.nextToken().getName().equals("SIGSTART"));
  }

  // ===================================== reading a signature ====================================

  @Test
  public void testReadUnsortedSignature() {
    ParsingStatus status = makeStatus("(SIG (f 2) (a 0) (g 7)) blaat");
    SymbolData data = TrsInputReader.readSignature(status);
    assertTrue(data.lookupFunctionSymbol("f").queryType().toString().equals("o ⇒ o ⇒ o"));
    assertTrue(data.lookupFunctionSymbol("a").queryType().toString().equals("o"));
    assertTrue(data.lookupFunctionSymbol("g").queryType().queryArity() == 7);
    assertTrue(status.nextToken().getText().equals("blaat"));
  }

  @Test
  public void testReadSortedSignatureWithOneNullaryConstant() {
    ParsingStatus status = makeStatus("(SIG (f -> int)) ->");
    SymbolData data = TrsInputReader.readSignature(status);
    assertTrue(data.lookupFunctionSymbol("f").queryType().toString().equals("int"));
    assertTrue(status.nextToken().getText().equals("->"));
  }

  @Test
  public void testReadSortedSignatureWithOneBinaryConstant() {
    ParsingStatus status = makeStatus("(SIG (* int int -> int)))");
    SymbolData data = TrsInputReader.readSignature(status);
    assertTrue(data.lookupFunctionSymbol("*").queryType().toString().equals("int ⇒ int ⇒ int"));
    assertTrue(status.nextToken().getText().equals(")"));
  }

  @Test
  public void testReadSortedSignatureWithVariousConstants() {
    ParsingStatus status = makeStatus("(SIG (* int int -> int)(f int -> bool)\n(true -> 9))");
    SymbolData data = TrsInputReader.readSignature(status);
    assertTrue(data.lookupFunctionSymbol("*").queryType().toString().equals("int ⇒ int ⇒ int"));
    assertTrue(data.lookupFunctionSymbol("f").queryType().toString().equals("int ⇒ bool"));
    assertTrue(data.lookupFunctionSymbol("true").queryType().toString().equals("9"));
  }

  @Test
  public void testMixedSignature() {
    ParsingStatus status = makeStatus("(SIG (f 2) (g int int -> int) (a 0) (hh 3 -> 4))");
    SymbolData data = TrsInputReader.readSignature(status);
    assertTrue(data.lookupFunctionSymbol("f").queryType().toString().equals("o ⇒ o ⇒ o"));
    assertTrue(data.lookupFunctionSymbol("g").queryType().toString().equals("int ⇒ int ⇒ int"));
    assertTrue(data.lookupFunctionSymbol("a").queryType().toString().equals("o"));
    assertTrue(data.lookupFunctionSymbol("hh").queryType().toString().equals("3 ⇒ 4"));
  }

  @Test
  public void testForgotBracketsOnceUnsorted() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("(SIG f 2) ping", collector);
    SymbolData data = TrsInputReader.readSignature(status);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:6: Expected an integer or sort declaration in brackets but got IDENTIFIER (f).\n"));
    // but recovery works!
    assertTrue(data.lookupFunctionSymbol("f").queryType().toString().equals("o ⇒ o ⇒ o"));
    assertTrue(status.nextToken().getText().equals("ping"));
   }

  @Test
  public void testForgotBracketsOnceSorted() {
    // SIG (f x y -> z)
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("(SIG f x y -> z) toot", collector);
    SymbolData data = TrsInputReader.readSignature(status);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:6: Expected an integer or sort declaration in brackets but got IDENTIFIER (f).\n"));
    // but recovery works!
    assertTrue(data.lookupFunctionSymbol("f").queryType().toString().equals("x ⇒ y ⇒ z"));
    assertTrue(status.nextToken().getText().equals("toot"));
  }

  @Test
  public void testForgotMultipleTimes() {
    // SIG (f 0 g a b -> zz hh -> int)
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("(SIG f 0 g a b -> zz hh -> int))", collector);
    SymbolData data = TrsInputReader.readSignature(status);
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:6: Expected an integer or sort declaration in brackets but got IDENTIFIER (f).\n" +
      "1:22: Expected an integer or sort declaration in brackets but got IDENTIFIER (hh).\n"));
    // but recovery works!
    assertTrue(data.lookupFunctionSymbol("f").queryType().toString().equals("0 ⇒ g ⇒ a ⇒ b ⇒ zz"));
    assertTrue(data.lookupFunctionSymbol("hh").queryType().toString().equals("int"));
    assertTrue(status.nextToken().getText().equals(")"));
  }

  @Test
  public void testReasonableDeclarationsWithoutArrow() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("(SIG (true bool) (false bool) (> int int -> bool)) a", collector);
    SymbolData data = TrsInputReader.readSignature(status);
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:12: Unexpected identifier: bool.  Expected an integer (for the extended TRS format) or " +
        "a sort declaration (for the MSTRS format).  Did you forget ->?\n" +
      "1:25: Unexpected identifier: bool.  Expected an integer (for the extended TRS format) or " +
        "a sort declaration (for the MSTRS format).  Did you forget ->?\n"));
    // but recovery works!
    assertTrue(data.lookupFunctionSymbol("false").queryType().toString().equals("bool"));
    assertTrue(data.lookupFunctionSymbol("true").queryType().toString().equals("bool"));
    assertTrue(data.lookupFunctionSymbol(">").queryType().toString().equals("int ⇒ int ⇒ bool"));
    assertTrue(status.nextToken().getText().equals("a"));
  }

  @Test
  public void testUnreasonableDeclarationWithoutArrow() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("(SIG (> int int bool) (f 1))", collector);
    SymbolData data = TrsInputReader.readSignature(status);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:21: Expected IDENTIFIER (a sort) or the sort declaration arrow (->) but got " +
        "BRACKETCLOSE ()).\n"));
    assertTrue(data.lookupFunctionSymbol(">").queryType().toString().equals("int ⇒ int ⇒ bool"));
    assertTrue(data.lookupFunctionSymbol("f").queryType().toString().equals("o ⇒ o"));
   }

  @Test
  public void testBadIntegerInDeclaration() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("(SIG (f 0) (g 00) (h -1) (b 3))", collector);
    SymbolData data = TrsInputReader.readSignature(status);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:22: Cannot set arity below 0.\n"));
    assertTrue(data.lookupFunctionSymbol("f").queryType().toString().equals("o"));
    assertTrue(data.lookupFunctionSymbol("g").queryType().toString().equals("o"));
    assertTrue(data.lookupFunctionSymbol("h").queryType().toString().equals("o"));
    assertTrue(data.lookupFunctionSymbol("b").queryType().toString().equals("o ⇒ o ⇒ o ⇒ o"));
  }

  @Test
  public void testDoubleDeclaration() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("(SIG (f 0) (g 3) (f 1) (g 3))", collector);
    SymbolData data = TrsInputReader.readSignature(status);
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:19: Redeclaration of function symbol f.\n" +
      "1:25: Redeclaration of function symbol g.\n"));
    assertTrue(data.lookupFunctionSymbol("f").queryType().toString().equals("o"));
    assertTrue(data.lookupFunctionSymbol("g").queryType().toString().equals("o ⇒ o ⇒ o ⇒ o"));
  }

  @Test(expected = cora.exceptions.ParseError.class)
  public void testStupidDeclaration() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("(SIG (f : (a -> b) -> c))");
    SymbolData data = TrsInputReader.readSignature(status);
    // this is stupid enough not to try recovery
  }

  @Test
  public void testUnfinishedDeclarationEof() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("(SIG (f 2) (a 0) (g 7)", collector);
    SymbolData data = TrsInputReader.readSignature(status);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:23: Unexpected end of input while reading (SIG.\n"));
    assertTrue(data.lookupFunctionSymbol("f").queryType().toString().equals("o ⇒ o ⇒ o"));
    assertTrue(data.lookupFunctionSymbol("a").queryType().toString().equals("o"));
    assertTrue(data.lookupFunctionSymbol("g").queryArity() == 7);
    assertTrue(status.nextToken().isEof());
  }

  @Test
  public void testUnfinishedDeclarationOther() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("(SIG (f 2) (a 0) (g 7) (RULES 12))", collector);
    SymbolData data = TrsInputReader.readSignature(status);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:24: Unexpected (RULES; did you forget ) to close (SIG?\n"));
    assertTrue(data.lookupFunctionSymbol("f").queryType().toString().equals("o ⇒ o ⇒ o"));
    assertTrue(data.lookupFunctionSymbol("a").queryType().toString().equals("o"));
    assertTrue(data.lookupFunctionSymbol("g").queryArity() == 7);
    assertTrue(status.nextToken().getText().equals("(RULES"));
  }

  // =================================== reading term structure ===================================

  @Test
  public void testReadUnfinishedOpening() {
    try { TrsInputReader.readUnsortedTermFromString("a(", ""); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "2:3: Expected an identifier (variable or function name) but got end of input.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadMissingCloseBracket() {
    try { TrsInputReader.readSortedTermFromString("f(a, b(x)", ""); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "2:10: Expected a comma or closing bracket but got end of input.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadArrowAfterComma() {
    try { TrsInputReader.readUnsortedTermFromString("f(a, b(x), -> c)", ""); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "2:12: Expected an identifier (variable or function name) but got ARROW (->).\n"));
      return;
    }
    assertTrue(false);
  }
 
  // ================================== reading an unsorted term ==================================

  @Test
  public void testReadUnsortedSingleVariable() {
    Term term = TrsInputReader.readUnsortedTermFromString("x", "x");
    assertTrue(term.isVariable());
    assertTrue(term.toString().equals("x"));
  }

  @Test
  public void testReadUnsortedSingleConstant() {
    Term term = TrsInputReader.readUnsortedTermFromString("x", "");
    assertTrue(term.isConstant());
    assertTrue(term.toString().equals("x"));
  }

  @Test
  public void testReadUnsortedEmptyBracketList() {
    Term term = TrsInputReader.readUnsortedTermFromString("x()", "");
    assertTrue(term.isConstant());
    assertTrue(term.toString().equals("x"));
  }

  @Test
  public void testReadUnsortedSameSymbolTwice() {
    Term term = TrsInputReader.readUnsortedTermFromString("f(f(x))", "x");
    assertTrue(term.toString().equals("f(f(x))"));
    assertTrue(term.queryRoot().equals(term.queryArgument(1).queryRoot()));
  }

  @Test
  public void testReadUnsortedSameVariableTwice() {
    Term term = TrsInputReader.readUnsortedTermFromString("f(x, x)", "x y");
    assertTrue(term.toString().equals("f(x, x)"));
    assertTrue(term.queryArgument(1) == term.queryArgument(2));
  }

  @Test
  public void testReadUnsortedComplexTerm() {
    Term term = TrsInputReader.readUnsortedTermFromString("f(g(x, y), h(x, u(), g(a, y)))",
                                                          "x y u v");
    assertTrue(term.toString().equals("f(g(x, y), h(x, u, g(a, y)))"));
    assertTrue(term.vars().size() == 3);
  }

  @Test
  public void testReadMultipleInconsistencies() {
    try { TrsInputReader.readUnsortedTermFromString("f(a, a(, x), g(y, ), a(b)", "x y"); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "2:8: Expected an identifier (variable or function name) but got COMMA (,).\n" +
        "2:19: Expected an identifier (variable or function name) but got BRACKETCLOSE ()).\n" +
        "2:26: Expected a comma or closing bracket but got end of input.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testUnsortedAbusedVariable() {
    try { TrsInputReader.readUnsortedTermFromString("x(a)", "x"); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals("2:1: Variable x used as root of a functional term.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testUnsortedInconsistentArities() {
    try { TrsInputReader.readUnsortedTermFromString("g(f(x, f(a)), a(y))", "x y"); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "2:3: Function symbol f was previously used with 1 arguments, but is here used with 2.\n" +
        "2:15: Function symbol a was previously used with 0 arguments, but is here used with 1.\n"
      ));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testUnsortedWeirdnessInsideSubTerm() {
    try { TrsInputReader.readUnsortedTermFromString("f(a, g(b, ), g(x, y))", "x y"); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "2:11: Expected an identifier (variable or function name) but got BRACKETCLOSE ()).\n"));
      return;
    }
    assertTrue(false);
  }

  // ==================================== reading a sorted term ===================================

  @Test
  public void testReadSortedSingleVariable() {
    Term term = TrsInputReader.readSortedTermFromString("x", "", TypeFactory.createSort("u"));
    assertTrue(term.isVariable());
    assertTrue(term.toString().equals("x"));
    assertTrue(term.queryType().toString().equals("u"));
  }

  @Test
  public void testReadSortedSingleConstant() {
    Term term = TrsInputReader.readSortedTermFromString("x", "(x -> a)");
    assertTrue(term.isConstant());
    assertTrue(term.toString().equals("x"));
    assertTrue(term.queryType().toString().equals("a"));
  }

  @Test
  public void testGuessType() {
    Term term = TrsInputReader.readSortedTermFromString("x", "");
    assertTrue(term.isVariable());
    assertTrue(term.toString().equals("x"));
    assertTrue(term.queryType().toString().equals("o"));
  }

  @Test
  public void testReadSimpleCorrectTerm() {
    String sig = "(f B A -> C) (g A A -> B) (a -> A)";
    Term t = TrsInputReader.readSortedTermFromString("f(g(x, y), a)", sig);
    FunctionSymbol f = t.queryRoot();
    FunctionSymbol g = t.queryArgument(1).queryRoot();
    FunctionSymbol a = t.queryArgument(2).queryRoot();
    Variable x = t.queryArgument(1).queryArgument(1).queryVariable();
    Variable y = t.queryArgument(1).queryArgument(2).queryVariable();
    Term combi = TermFactory.createApp(f, TermFactory.createApp(g, x, y), a);
    assertTrue(t.equals(combi));
  }

  @Test
  public void testReadTermWithSameVariableTwice() {
    String sig = "(f B B -> A) (g A A -> B)";
    Term t = TrsInputReader.readSortedTermFromString("f(g(x,y),g(x,a))", sig);
    assertTrue(t.toString().equals("f(g(x, y), g(x, a))"));
    assertTrue(t.queryArgument(1).queryArgument(1) == t.queryArgument(2).queryArgument(1));
  }

  @Test
  public void testVariableUsedAsFunction() {
    try { TrsInputReader.readSortedTermFromString("f(x, x(a))", "(a 1) (f 2)"); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "2:6: Variable x used as a function symbol!\n" +
        "2:8: Function symbol a was declared with 1 arguments, but is used here with 0.\n"
      ));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testUndeclaredUsedAsFunction() {
    try { TrsInputReader.readSortedTermFromString("f(y, x(a))", "(a 1) (f 2)"); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "2:6: Undeclared function symbol: x.\n" +
        "2:8: Function symbol a was declared with 1 arguments, but is used here with 0.\n"
      ));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadTermWithSortErrors() {
    String sig = "(f A B -> C) (g A B -> A) (a -> B)";
    try { TrsInputReader.readSortedTermFromString("f(g(x, y), g(a, g(a, x)))", sig); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "2:12: Expected term of type B, but got term g(a, g(a, x)) of type A.\n" +
        "2:14: Expected term of type A, but got term a of type B.\n" +
        "2:17: Expected term of type B, but got term g(a, x) of type A.\n" +
        "2:19: Expected term of type A, but got term a of type B.\n" +
        "2:22: Expected term of type B, but got variable x which was previously used with type A.\n"
      ));
    }
  }

  @Test
  public void testReadTermWithArityErrors() {
    String sig = "(f A B -> C) (g A A -> A) (a -> B)";
    try { TrsInputReader.readSortedTermFromString("f(g(x), z, g(x, a))", sig); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "2:1: Function symbol f was declared with 2 arguments, but is used here with 3.\n" +
        "2:3: Function symbol g was declared with 2 arguments, but is used here with 1.\n" +
        "2:17: Expected term of type A, but got term a of type B.\n"
      ));
    }
  }

  @Test
  public void readSameUndeclaredSymbolTwice() {
    String sig = "(f A A -> B) (a -> A)";
    try { TrsInputReader.readSortedTermFromString("f(g(a), g(x))", sig); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "2:3: Undeclared function symbol: g.\n" +
        "2:9: Undeclared function symbol: g.\n"
      ));
    }
  }

  // ======================================== reading rules =======================================

  @Test
  public void testReadUnsortedRulesWithoutSymbolsDeclared() {
    SymbolData data = new SymbolData();
    ErrorCollector collector = new ErrorCollector(10);
    data.addVariable(TermFactory.createVar("x"));
    data.addVariable(TermFactory.createVar("y"));
    data.addVariable(TermFactory.createVar("z"));
    ParsingStatus status = makeStatus("(RULES" +
      "  f(x,s(y)) -> f(s(x),y)" +
      "  f(x,0) -> x" +
      ") test", collector);
    ArrayList<Rule> rules = TrsInputReader.readRules(status, data, false);
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(rules.size() == 2);
    assertTrue(rules.get(0).toString().equals("f(x, s(y)) → f(s(x), y)"));
    assertTrue(rules.get(1).toString().equals("f(x, 0) → x"));
    assertTrue(rules.get(0).queryLeftSide().vars().size() == 2);
    assertTrue(status.nextToken().getText().equals("test"));
  }

  @Test
  public void testReadUnsortedRulesWithSymbolsPredeclared() {
    SymbolData data = new SymbolData();
    ErrorCollector collector = new ErrorCollector(10);
    data.addVariable(TermFactory.createVar("x"));
    data.addVariable(TermFactory.createVar("y"));
    data.addFunctionSymbol(TermFactory.createConstant("f", 2));
    data.addFunctionSymbol(TermFactory.createConstant("s", 1));
    data.addFunctionSymbol(TermFactory.createConstant("0", 0));
    ParsingStatus status = makeStatus("(RULES" +
      "  f(x,s(y)) -> f(s(x),y)" +
      "  f(x,0) -> x" +
      ") test", collector);
    ArrayList<Rule> rules = TrsInputReader.readRules(status, data, true);
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(rules.size() == 2);
    assertTrue(rules.get(0).toString().equals("f(x, s(y)) → f(s(x), y)"));
    assertTrue(rules.get(1).toString().equals("f(x, 0) → x"));
    assertTrue(rules.get(0).queryLeftSide().vars().size() == 2);
    assertTrue(status.nextToken().getText().equals("test"));
  }

  @Test
  public void testReadSingleSortedRule() {
    SymbolData data = new SymbolData();
    ErrorCollector collector = new ErrorCollector(10);
    Type iint = TypeFactory.createSort("Int");
    Type iii = TypeFactory.createArrow(iint, TypeFactory.createArrow(iint, iint));
    data.addFunctionSymbol(TermFactory.createConstant("+", iii));
    data.addFunctionSymbol(TermFactory.createConstant("s", TypeFactory.createArrow(iint, iint)));
    ParsingStatus status = makeStatus("(RULES +(x, s ( y)) -> s(+(y,x))))");
    ArrayList<Rule> rules = TrsInputReader.readRules(status, data, true);
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(rules.size() == 1);
    assertTrue(rules.get(0).toString().equals("+(x, s(y)) → s(+(y, x))"));
    assertTrue(rules.get(0).queryRightSide().vars().size() == 2);
    assertTrue(status.nextToken().getText().equals(")"));
  }

  @Test
  public void testReadSortedRuleWhereVariableHasDifferentTypesInDifferentRules() {
    SymbolData data = new SymbolData();
    ErrorCollector collector = new ErrorCollector(10);
    Type tint = TypeFactory.createSort("Int");
    Type tbool = TypeFactory.createSort("Bool");
    data.addFunctionSymbol(TermFactory.createConstant("f", TypeFactory.createArrow(tint, tint)));
    data.addFunctionSymbol(TermFactory.createConstant("g", TypeFactory.createArrow(tbool, tbool)));
    ParsingStatus status = makeStatus("(RULES f(x) -> x g(x) -> x)");
    ArrayList<Rule> rules = TrsInputReader.readRules(status, data, true);
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(rules.size() == 2);
    assertTrue(rules.get(0).queryRightSide().queryVariable() !=
               rules.get(1).queryRightSide().queryVariable());
  }

  @Test
  public void testReadSortedRulesWhereSomeSymbolIsUndeclared() {
    SymbolData data = new SymbolData();
    ErrorCollector collector = new ErrorCollector(10);
    data.addFunctionSymbol(TermFactory.createConstant("f", 2));
    data.addFunctionSymbol(TermFactory.createConstant("0", 0));
    ParsingStatus status = makeStatus("(RULES" +
      "  f(x,s(y)) -> f(s(x),y)\n" +
      "  f(x,0) -> g(x)" +
      ") test", collector);
    ArrayList<Rule> rules = TrsInputReader.readRules(status, data, true);
    assertTrue(collector.queryErrorCount() == 4);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:13: Undeclared function symbol: s.\n" +
      "1:24: Undeclared function symbol: s.\n" +
      "1:9: right-hand side of rule [f(x, s(y)) → f(s(x), y)] contains variable y which does " +
        "not occur on the left.\n" +
      "2:13: Undeclared function symbol: g.\n"));
        // the third error is given because the variable below s is not recognised as the same
        // variable; this does not cause a problem in the last case, because then x is already
        // known when it occurs in a type-mysterious place
    assertTrue(rules.size() == 1);
    assertTrue(rules.get(0).toString().equals("f(x, 0) → g(x)"));
    assertTrue(rules.get(0).queryLeftSide().vars().size() == 1);
  }

  @Test
  public void testReadRuleWhereLeftHasStructureProblems() {
    SymbolData data = new SymbolData();
    ErrorCollector collector = new ErrorCollector(10);
    data.addFunctionSymbol(TermFactory.createConstant("f", 2));
    data.addFunctionSymbol(TermFactory.createConstant("0", 0));
    ParsingStatus status = makeStatus("(RULES" +
      "  f(x, s(y) -> f(g(x),y)\n" +
      "  f(x,0) -> g(x)" +
      ") test", collector);
    ArrayList<Rule> rules = TrsInputReader.readRules(status, data, true);
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:19: Expected a comma or closing bracket but got ARROW (->).\n" +
      "2:13: Undeclared function symbol: g.\n"));
    assertTrue(rules.size() == 1);
  }

  @Test
  public void testReadRuleWhereRightHasStructureProblems() {
    SymbolData data = new SymbolData();
    ErrorCollector collector = new ErrorCollector(10);
    data.addVariable(TermFactory.createVar("x"));
    data.addVariable(TermFactory.createVar("y"));
    ParsingStatus status = makeStatus("(RULES" +
      "  f(x, s(y)) -> f(g(x),,y)\n" +
      "  f(x) -> f(x, x)" +
      ") test", collector);
    ArrayList<Rule> rules = TrsInputReader.readRules(status, data, false);
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:30: Expected an identifier (variable or function name) but got COMMA (,).\n" +
      "2:11: Function symbol f was previously used with 1 arguments, but is here used with 2.\n"));
    assertTrue(rules.size() == 1);
  }

  @Test
  public void testRulesWithMissingBracketOnRight() {
    SymbolData data = new SymbolData();
    ErrorCollector collector = new ErrorCollector(10);
    data.addFunctionSymbol(TermFactory.createConstant("f", 2));
    data.addFunctionSymbol(TermFactory.createConstant("0", 0));
    ParsingStatus status = makeStatus("(RULES " +
      "f(x, s(y)) -> f(g(x),y\n" +
      "f(x,0) -> g(x)\n" +
      "0 -> 0\n" +
      ") test", collector);
    ArrayList<Rule> rules = TrsInputReader.readRules(status, data, true);
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals(
      "2:1: Expected a comma or closing bracket but got IDENTIFIER (f).\n" +
      "2:8: Expected a comma or closing bracket but got ARROW (->).\n"
    ));
    assertTrue(rules.size() == 1);
    assertTrue(rules.get(0).toString().equals("0 → 0"));
  }

  @Test
  public void testRuleWithInconsistentTermTyping() {
    SymbolData data = new SymbolData();
    ErrorCollector collector = new ErrorCollector(10);
    Type iint = TypeFactory.createSort("Int");
    Type ibool = TypeFactory.createSort("Bool");
    data.addFunctionSymbol(TermFactory.createConstant("f", TypeFactory.createArrow(iint, ibool)));
    data.addFunctionSymbol(TermFactory.createConstant("g", TypeFactory.createArrow(iint, iint)));
    ParsingStatus status = makeStatus("(RULES f(x) -> g(x))", collector);
    ArrayList<Rule> rules = TrsInputReader.readRules(status, data, true);
    assertTrue(rules.size() == 1);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:16: Expected term of type Bool, but got term g(x) of type Int.\n"
    ));
  }

  @Test
  public void testRuleWithInconsistentVariableTyping() {
    SymbolData data = new SymbolData();
    ErrorCollector collector = new ErrorCollector(10);
    Type iint = TypeFactory.createSort("Int");
    Type ibool = TypeFactory.createSort("Bool");
    data.addFunctionSymbol(TermFactory.createConstant("f", TypeFactory.createArrow(iint, iint)));
    data.addFunctionSymbol(TermFactory.createConstant("g", TypeFactory.createArrow(ibool, iint)));
    ParsingStatus status = makeStatus("(RULES f(x) -> g(x))\n", collector);
    ArrayList<Rule> rules = TrsInputReader.readRules(status, data, true);
    assertTrue(rules.size() == 1);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:18: Expected term of type Bool, but got variable x which was previously used with type " +
        "Int.\n"
    ));
  }

  @Test
  public void testRuleWithFreshVariableOnRightSide() {
    SymbolData data = new SymbolData();
    ErrorCollector collector = new ErrorCollector(10);
    data.addFunctionSymbol(TermFactory.createConstant("f", 2));
    ParsingStatus status = makeStatus("(RULES f(x, y) -> f(y, z))", collector);
    ArrayList<Rule> rules = TrsInputReader.readRules(status, data, true);
    assertTrue(rules.size() == 0);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:8: right-hand side of rule [f(x, y) → f(y, z)] contains variable z which does not " +
        "occur on the left.\n"));
  }

  @Test
  public void testSortedRuleWithLeftVariable() {
    SymbolData data = new SymbolData();
    ErrorCollector collector = new ErrorCollector(10);
    data.addFunctionSymbol(TermFactory.createConstant("f", 2));
    ParsingStatus status = makeStatus("(RULES x -> f(x, x))", collector);
    ArrayList<Rule> rules = TrsInputReader.readRules(status, data, true);
    assertTrue(rules.size() == 0);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:8: The left-hand side of a rule is not allowed to be a variable.\n"));
  }

  @Test
  public void testUnsortedRuleWithLeftVariable() {
    SymbolData data = new SymbolData();
    ErrorCollector collector = new ErrorCollector(10);
    data.addVariable(TermFactory.createVar("x"));
    ParsingStatus status = makeStatus("(RULES x -> f(x, x))", collector);
    ArrayList<Rule> rules = TrsInputReader.readRules(status, data, false);
    assertTrue(rules.size() == 0);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:8: illegal rule [x → f(x, x)] with a variable as the left-hand side.\n"));
    assertTrue(status.nextToken().isEof());
  }

  // ===================================== reading a full TRS =====================================

  @Test
  public void testReadSimpleUnsortedTrs() {
    TRS trs = TrsInputReader.readTrsFromString("(VAR x y)\n" +
                                                 "(RULES\n" +
                                                 "  +(x, 0) -> x\n" +
                                                 "  +(x, s(y)) -> s(+(x,y))\n" +
                                                 ")");
    assertTrue(trs.lookupSymbol("0").queryType().equals(TypeFactory.createSort("o")));
    assertTrue(trs.lookupSymbol("s").queryType().toString().equals("o ⇒ o"));
    assertTrue(trs.lookupSymbol("+").queryType().toString().equals("o ⇒ o ⇒ o"));
    assertTrue(trs.lookupSymbol("x") == null);
    assertTrue(trs.lookupSymbol("y") == null);
    assertTrue(trs.queryRuleCount() == 2);
    assertTrue(trs.queryRule(0).toString().equals("+(x, 0) → x"));
    assertTrue(trs.queryRule(1).toString().equals("+(x, s(y)) → s(+(x, y))"));
  }

  @Test
  public void testReadUnsortedTrsWithSignatureAndComment() {
    String str = "(VAR x ys xs)\n" +
                 "(SIG (nil 0) (cons 2) (append 2) (0 0) (s 1))\n" +
                 "(RULES\n" +
                 "  append(nil, ys) -> ys\n" +
                 "  append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n" +
                 ") (COMMENT hello world!)";
    TRS trs = TrsInputReader.readTrsFromString(str);
    FunctionSymbol append = trs.lookupSymbol("append");
    FunctionSymbol cons = trs.lookupSymbol("cons");
    FunctionSymbol nil = trs.lookupSymbol("nil");
    FunctionSymbol zero = trs.lookupSymbol("0");
    FunctionSymbol suc = trs.lookupSymbol("s");
    Term s = TermFactory.createApp(cons, suc.apply(zero), nil);
    Term t = TermFactory.createApp(cons, zero, TermFactory.createApp(cons, zero, nil));
    Term q = TermFactory.createApp(append, s, t);
    assertTrue(q.toString().equals("append(cons(s(0), nil), cons(0, cons(0, nil)))"));
    q = trs.leftmostInnermostReduce(q);
    q = trs.leftmostInnermostReduce(q);
    assertTrue(q.toString().equals("cons(s(0), cons(0, cons(0, nil)))"));
    assertTrue(trs.leftmostInnermostReduce(q) == null);
  }

  @Test
  public void testReadSortedTrs() {
    String str = "(SIG " +
                 "  (app   List List -> List)" +
                 "  (cons  Nat List -> List)" +
                 "  (nil   -> List)" +
                 "  (s     Nat -> Nat)" +
                 "  (0     -> Nat)" +
                 "  (len   List -> Nat)" +
                 ")(RULES" +
                 "  app(nil,ys) -> ys" +
                 "  app(cons(x,xs),ys) -> cons(x,app(xs,ys))" +
                 "  len(nil) -> 0" +
                 "  len(cons(x, xs)) -> s(len(xs))" +
                 ") (COMMENT this is :) a comment) ";
    TRS trs = TrsInputReader.readTrsFromString(str);
    FunctionSymbol app = trs.lookupSymbol("app");
    assertTrue(app.queryType().toString().equals("List ⇒ List ⇒ List"));
    assertTrue(trs.queryRuleCount() == 4);
    Rule appbase = trs.queryRule(0);
    Rule lenadvanced = trs.queryRule(3);
    assertTrue(appbase.toString().equals("app(nil, ys) → ys"));
    assertTrue(lenadvanced.toString().equals("len(cons(x, xs)) → s(len(xs))"));
    Term left = lenadvanced.queryLeftSide();
    assertTrue(left.queryType().equals(TypeFactory.createSort("Nat")));
    assertTrue(left.queryArgument(1).queryType().equals(TypeFactory.createSort("List")));
  }

  @Test
  public void testReadSortedTrsWithVariableTypeChange() {
    String str = "(SIG (f a -> a) (g b -> b)) (RULES f(x) -> x g(x) -> x)";
    TRS trs = TrsInputReader.readTrsFromString(str);
    Rule a = trs.queryRule(0);
    Rule b = trs.queryRule(1);
    assertFalse(a.queryRightSide().queryType().equals(b.queryRightSide().queryType()));
  }

  @Test
  public void testReadTrsWithMoreAfterEnding() {
    String str = "(VAR x y) (RULES f(x) -> y) uh oh!";
    try { TrsInputReader.readTrsFromString(str); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:18: right-hand side of rule [f(x) → y] contains variable y which does not occur on " +
          "the left.\n" +
        "1:29: Expected end of input but got IDENTIFIER (uh).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadTrsWithMoreAfterComment() {
    String str = "(VAR x) (RULES f(x) -> g(x,)) (COMMENT extra comma ) there...) you see?";
    try { TrsInputReader.readTrsFromString(str); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:28: Expected an identifier (variable or function name) but got BRACKETCLOSE ()).\n" +
        "1:64: Unexpected token: you; expected end of input following comment.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testTrsWithUnclosedComment() {
    String str = "(RULES a -> a) (COMMENT bing";
    try { TrsInputReader.readTrsFromString(str); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals("1:16: Unclosed comment.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testMixSigAndVar() {
    String str = "(SIG (f 2)) (VAR x) (RULES I can just type nonsense here";
    try { TrsInputReader.readTrsFromString(str); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:13: Expected rules declaration but got VARSDECSTART ((VAR).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testMissingRules() {
    String str = "(SIG (f 2)) (COMMENT an empty file";
    try { TrsInputReader.readTrsFromString(str); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:13: Expected rules declaration but got COMMENTSTART ((COMMENT).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void readUnsortedTrsWithIncompleteSignature() {
    String str = "(VAR x ys xs)\n" +
                 "(SIG (nil 0) (cons 2) (0 0) (s 1))\n" +
                 "(RULES\n" +
                 "  append(nil, ys) -> ys\n" +
                 "  append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n" +
                 ")";
    try { TrsInputReader.readTrsFromString(str); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "4:3: Undeclared function symbol: append.\n" +
        "5:3: Undeclared function symbol: append.\n" +
        "5:38: Undeclared function symbol: append.\n" +
        "5:3: right-hand side of rule [append(cons(x, xs), ys) → cons(x, append(xs, ys))] " +
          "contains variable ys which does not occur on the left.\n"));
      return;
    }
    assertTrue(false);
  }

  // ============================== reading terms when a TRS is given =============================

  @Test
  public void testReadTermGivenTRS() {
    String str = "(VAR x ys xs)\n" +
                 "(RULES\n" +
                 "  append(nil, ys) -> ys\n" +
                 "  append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n" +
                 ")";
    TRS trs = TrsInputReader.readTrsFromString(str);
    Term t = TrsInputReader.readTermFromString("append(cons(x, nil), lst)", trs);
    assertTrue(t.vars().size() == 2);
  }

  @Test
  public void testReadTermWithUndeclaredSymbol() {
    String str = "(VAR x ys xs)\n" +
                 "(RULES\n" +
                 "  append(nil, ys) -> ys\n" +
                 "  append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n" +
                 ")";
    TRS trs = TrsInputReader.readTrsFromString(str);
    try { TrsInputReader.readTermFromString("append(cons(s(0), nil), lst)", trs); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals("1:13: Undeclared function symbol: s.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadTermTooMuch() {
    String str = "(VAR x ys xs)\n" +
                 "(RULES\n" +
                 "  append(nil, ys) -> ys\n" +
                 "  append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n" +
                 ")";
    TRS trs = TrsInputReader.readTrsFromString(str);
    try { TrsInputReader.readTermFromString("append(cons(x, nil), lst) xx", trs); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:27: Expected end of string but got IDENTIFIER (xx).\n"));
      return;
    }
    assertTrue(false);
  }
}

