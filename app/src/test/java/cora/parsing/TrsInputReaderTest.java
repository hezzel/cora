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

