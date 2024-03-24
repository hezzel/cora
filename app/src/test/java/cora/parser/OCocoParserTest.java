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

package cora.parser;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.exceptions.ParseError;
import cora.utils.LookupMap;
import cora.parser.lib.ErrorCollector;
import cora.parser.Parser.*;

public class OCocoParserTest {
  // ====================================== reading a varlist =====================================

  @Test
  public void testReadCorrectVarList() {
    ParserProgram prog = OCocoParser.readProgramFromString("(VAR x y) (RULES a ->b b -> a)");
    assertTrue(prog.fundecs().isEmpty());
    assertTrue(prog.rules().size() == 2);
    LookupMap<ParserDeclaration> vardec = prog.rules().get(0).vars();
    assertTrue(vardec != null);
    assertTrue(vardec == prog.rules().get(1).vars());
    assertTrue(vardec.get("x") != null);
    assertTrue(vardec.get("y") != null);
    assertTrue(vardec.get("z") == null);
    assertTrue(vardec.get("x").type().toString().equals("o"));
  }

  @Test
  public void testReadVarListWithIllegalTokens() {
    try { OCocoParser.readProgramFromString("(VAR x -> y ( 23) =="); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:8: Unexpected token: -> (ARROW); expected a variable name\n"));
    }
  }

  @Test
  public void testReadVarListWithDoubleDeclaration() {
    ErrorCollector col = new ErrorCollector();
    LookupMap<ParserDeclaration> vardecs = OCocoParser.readDeclarations("(VAR x y x 12 y)", col);
    assertTrue(vardecs.get("x") != null);
    assertTrue(vardecs.get("y") != null);
    assertTrue(vardecs.get("12") != null);

    assertTrue(col.queryErrorCount() == 2);
    assertTrue(col.queryCollectedMessages().equals(
      "1:10: Double declaration of variable x\n" +
      "1:15: Double declaration of variable y\n"));
  }

  @Test
  public void testReadVarListThatDoesNotEnd() {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram result =
      OCocoParser.readProgramFromString("  (VAR x y 12 ", collector);

    assertTrue(result.fundecs().size() == 0);
    assertTrue(result.rules().size() == 0);

    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:3: Encountered end of input while reading varlist; no closing bracket given.\n" +
      "2:1: Expected rules declaration but got end of input.\n"));
  }

  @Test
  public void testReadVarListWithRuleListInTheMiddle() {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram result =
      OCocoParser.readProgramFromString("  (VAR x y 12 (RULES a -> a))", collector);

    assertTrue(result.rules().size() == 1);
    LookupMap<ParserDeclaration> vardecs = result.rules().get(0).vars();
    assertTrue(vardecs.containsKey("x"));
    assertTrue(vardecs.containsKey("y"));
    assertTrue(vardecs.containsKey("12"));

    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:15: Unexpected (RULES while reading varlist; did you forget a closing bracket?\n" +
      "1:29: Expected end of input but got BRACKETCLOSE ()).\n"));
  }

  @Test
  public void testReadVarListWithFatalProblems() {
    ErrorCollector collector = new ErrorCollector();
    try {
      OCocoParser.readProgramFromString("  (VAR x \ny x ( 12 -> y y (RULES ))", collector);
    }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "2:3: Double declaration of variable x\n" +
        "2:5: Unexpected token: ( (BRACKETOPEN); expected a variable name\n"));
      return;
    }
    assertTrue(false);
  }

  // ===================================== reading a signature ====================================

  @Test
  public void testReadUnsortedSignature() {
    ParserProgram result =
      OCocoParser.readProgramFromString("(SIG (f 2) (a 0) (g 7)) (RULES )");
    assertTrue(result.fundecs().get("f").type().toString().equals("o → o → o"));
    assertTrue(result.fundecs().get("a").type().toString().equals("o"));
    assertTrue(result.fundecs().get("g").type().queryArity() == 7);
    assertTrue(result.rules().size() == 0);
  }

  @Test
  public void testReadSortedSignatureWithOneNullaryConstant() {
    ParserProgram result =
      OCocoParser.readProgramFromString("(SIG (f -> int)) (RULES a -> a)");
    assertTrue(result.fundecs().get("f").type().toString().equals("int"));
    assertTrue(result.fundecs().size() == 1);
    assertTrue(result.rules().get(0).vars().isEmpty());
  }

  @Test
  public void testReadSortedSignatureWithOneBinaryConstant() {
    LookupMap<ParserDeclaration> sig =
      OCocoParser.readDeclarations("(SIG (* int int -> int))");
    assertTrue(sig.get("*").type().toString().equals("int → int → int"));
    assertTrue(sig.size() == 1);
  }

  @Test
  public void testReadSortedSignatureWithVariousConstants() {
    LookupMap<ParserDeclaration> sig = OCocoParser.readDeclarations(
      "(SIG (* int int -> int)(f int -> bool)\n(true -> 9))");
    assertTrue(sig.size() == 3);
    assertTrue(sig.get("*").type().toString().equals("int → int → int"));
    assertTrue(sig.get("f").type().toString().equals("int → bool"));
    assertTrue(sig.get("true").type().toString().equals("9"));
  }

  @Test
  public void testMixedSignature() {
    ErrorCollector collector = new ErrorCollector();
    LookupMap<ParserDeclaration> sig = OCocoParser.readDeclarations(
      "(SIG (f 2) (g int int -> int) (a 0) (hh 3 -> 4)) (RULES )", collector);

    assertTrue(sig.size() == 4);
    assertTrue(sig.get("f").type().toString().equals("o → o → o"));
    assertTrue(sig.get("g").type().toString().equals("int → int → int"));
    assertTrue(sig.get("a").type().toString().equals("o"));
    assertTrue(sig.get("hh").type().toString().equals("3 → 4"));
    
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:50: Expected end of input but got RULESDECSTART ((RULES).\n"));
  }

  @Test
  public void testForgotBracketsOnceUnsorted() {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram result =
      OCocoParser.readProgramFromString("(SIG f 2) (RULES a -> a)", collector);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:6: Expected an integer or sort declaration in brackets but got IDENTIFIER (f).\n"));
    // but recovery works!
    assertTrue(result.fundecs().get("f").type().toString().equals("o → o → o"));
    assertTrue(result.rules().size() == 1);
  }

  @Test
  public void testForgotBracketsOnceSorted() {
    ErrorCollector collector = new ErrorCollector();
    LookupMap<ParserDeclaration> sig =
      OCocoParser.readDeclarations("(SIG f x y -> z) toot", collector);
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:6: Expected an integer or sort declaration in brackets but got IDENTIFIER (f).\n" +
      "1:18: Expected end of input but got IDENTIFIER (toot).\n"));
    // but recovery works!
    assertTrue(sig.get("f").type().toString().equals("x → y → z"));
  }

  @Test
  public void testForgotMultipleTimes() {
    ErrorCollector collector = new ErrorCollector();
    LookupMap<ParserDeclaration> sig =
      OCocoParser.readDeclarations("(SIG f 0 g a b -> zz hh -> int)\n", collector);
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:6: Expected an integer or sort declaration in brackets but got IDENTIFIER (f).\n" +
      "1:22: Expected an integer or sort declaration in brackets but got IDENTIFIER (hh).\n"));
    // but recovery works!
    assertTrue(sig.get("f").type().toString().equals("0 → g → a → b → zz"));
    assertTrue(sig.get("hh").type().toString().equals("int"));
  }

  @Test
  public void testReasonableDeclarationsWithoutArrow() {
    ErrorCollector collector = new ErrorCollector();
    LookupMap<ParserDeclaration> sig =
      OCocoParser.readDeclarations("(SIG (true bool) (false bool) (> int int -> bool))", collector);
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:12: Unexpected identifier: bool.  Expected an integer (for the extended TRS format) or " +
        "a sort declaration (for the MSTRS format).  Did you forget ->?\n" +
      "1:25: Unexpected identifier: bool.  Expected an integer (for the extended TRS format) or " +
        "a sort declaration (for the MSTRS format).  Did you forget ->?\n"));
    // but recovery works!
    assertTrue(sig.get("false").type().toString().equals("bool"));
    assertTrue(sig.get("true").type().toString().equals("bool"));
    assertTrue(sig.get(">").type().toString().equals("int → int → bool"));
  }

  @Test
  public void testUnreasonableDeclarationWithoutArrow() {
    ErrorCollector collector = new ErrorCollector();
    LookupMap<ParserDeclaration> sig =
      OCocoParser.readDeclarations("(SIG (> int int bool) (f 1))", collector);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:21: Expected IDENTIFIER (a sort) or the sort declaration arrow (->) but got " +
        "BRACKETCLOSE ()).\n"));
    assertTrue(sig.get(">").type().toString().equals("int → int → bool"));
    assertTrue(sig.get("f").type().toString().equals("o → o"));
  }

  @Test
  public void testBadIntegerInDeclaration() {
    ErrorCollector collector = new ErrorCollector();
    LookupMap<ParserDeclaration> sig =
      OCocoParser.readDeclarations("(SIG (f 0) (g 00) (h -1) (b 3))", collector);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:22: Cannot set arity below 0.\n"));
    assertTrue(sig.get("f").type().toString().equals("o"));
    assertTrue(sig.get("g").type().toString().equals("o"));
    assertTrue(sig.get("h").type().toString().equals("o"));
    assertTrue(sig.get("b").type().toString().equals("o → o → o → o"));
  }

  @Test
  public void testDoubleDeclaration() {
    ErrorCollector collector = new ErrorCollector();
    LookupMap<ParserDeclaration> sig =
      OCocoParser.readDeclarations("(SIG (f 0) (g 3) (f 1) (g 3))", collector);
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:19: Redeclaration of function symbol f.\n" +
      "1:25: Redeclaration of function symbol g.\n"));
    assertTrue(sig.get("f").type().toString().equals("o"));
    assertTrue(sig.get("g").type().toString().equals("o → o → o → o"));
    assertTrue(sig.size() == 2);
  }

  @Test
  public void testStupidDeclaration() {
    ErrorCollector collector = new ErrorCollector();
    assertThrows(ParseError.class, () -> OCocoParser.readDeclarations("(SIG (f : (a -> b) -> c))"));
    // this is stupid enough not to try recovery
  }

  @Test
  public void testUnfinishedDeclarationEof() {
    ErrorCollector collector = new ErrorCollector();
    LookupMap<ParserDeclaration> sig =
      OCocoParser.readDeclarations("(SIG (f 2) (a 0) (g 7)", collector);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:23: Unexpected end of input while reading (SIG.\n"));
    assertTrue(sig.get("f").type().toString().equals("o → o → o"));
    assertTrue(sig.get("a").type().toString().equals("o"));
    assertTrue(sig.get("g").type().queryArity() == 7);
  }

  @Test
  public void testUnfinishedDeclarationOther() {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram result =
      OCocoParser.readProgramFromString("(SIG (f 2) (a 0) (g 7) (RULES 12 -> 11)", collector);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:24: Unexpected (RULES; did you forget ) to close (SIG?\n"));
    assertTrue(result.fundecs().get("f").type().toString().equals("o → o → o"));
    assertTrue(result.fundecs().get("a").type().toString().equals("o"));
    assertTrue(result.fundecs().get("g").type().queryArity() == 7);
    assertTrue(result.rules().size() == 1);
  }

  // ======================================== reading terms =======================================

  @Test
  public void testReadUnfinishedOpening() {
    ErrorCollector collector = new ErrorCollector();
    ParserTerm term = OCocoParser.readTerm("a(", collector);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals(
        "1:3: Expected an identifier (variable or function name) but got end of input.\n"));
    assertTrue(term.hasErrors());
    assertTrue(term.toString().equals("ERR(@(a, []))"));
  }

  @Test
  public void testReadMissingCloseBracket() {
    ErrorCollector collector = new ErrorCollector();
    ParserTerm term = OCocoParser.readTerm("f(a, b(x)", collector);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:10: Expected a comma or closing bracket but got end of input.\n"));
    assertTrue(term.hasErrors());
    assertTrue(term.toString().equals("ERR(@(f, [a, @(b, [x])]))"));
  }

  @Test
  public void testReadArrowAfterComma() {
    ErrorCollector collector = new ErrorCollector();
    ParserTerm term = OCocoParser.readTerm("f(a, b(x), -> c)", collector);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:12: Expected an identifier (variable or function name) but got ARROW (->).\n"));
    assertTrue(term.hasErrors());
    assertTrue(term.toString().equals("ERR(@(f, [a, @(b, [x])]))"));
  }

  @Test
  public void testReadSingleIdentifier() {
    ParserTerm term = OCocoParser.readTerm("x");
    assertFalse(term.hasErrors());
    assertTrue(term instanceof Parser.Identifier);
    assertTrue(term.toString().equals("x"));
  }

  @Test
  public void testReadEmptyBracketList() {
    ParserTerm term = OCocoParser.readTerm("x()");
    assertFalse(term.hasErrors());
    assertTrue(term instanceof Parser.Application);
    assertTrue(term.toString().equals("@(x, [])"));
  }

  @Test
  public void testReadComplexTerm() {
    ErrorCollector collector = new ErrorCollector();
    ParserTerm term = OCocoParser.readTerm("f(g(x, y), h(x, u(), g(a, y)))", collector);
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(term.toString().equals("@(f, [@(g, [x, y]), @(h, [x, @(u, []), @(g, [a, y])])])"));
  }

  @Test
  public void testReadTermWithMultipleInconsistencies() {
    ErrorCollector collector = new ErrorCollector();
    ParserTerm term = OCocoParser.readTerm("f(a, a(, x), g(y, ), a(b)", collector);
    assertTrue(collector.queryErrorCount() == 3);
    assertTrue(collector.queryCollectedMessages().equals(
        "1:8: Expected an identifier (variable or function name) but got COMMA (,).\n" +
        "1:19: Expected an identifier (variable or function name) but got BRACKETCLOSE ()).\n" +
        "1:26: Expected a comma or closing bracket but got end of input.\n"));
    assertTrue(term.toString().equals("ERR(@(f, [a, ERR(@(a, [x])), ERR(@(g, [y])), @(a, [b])]))"));
  }

  @Test
  public void testInconsistentAritiesAllowed() {
    ParserTerm term = OCocoParser.readTerm("g(f(x, f(a)), a(y))");
    assertTrue(term.toString().equals("@(g, [@(f, [x, @(f, [a])]), @(a, [y])])"));
  }

  @Test
  public void testWeirdnessInsideSubTerm() {
    ErrorCollector collector = new ErrorCollector();
    ParserTerm term = OCocoParser.readTerm("f(a, g(b, ), g(x, y))", collector);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:11: Expected an identifier (variable or function name) but got BRACKETCLOSE ()).\n"));
    assertTrue(term.toString().equals("@(f, [a, ERR(@(g, [b])), @(g, [x, y])])"));
  }

  // ======================================== reading rules =======================================

  @Test
  public void testReadCorrectRule() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = OCocoParser.readRule("f(x,s(y)) -> f(s(x), y)", collector);
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(rule.toString().equals("{ [] } @(f, [x, @(s, [y])]) → @(f, [@(s, [x]), y])"));
  }

  @Test
  public void testReadRuleWithoutArrow() {
    try {OCocoParser.readRule("a a", new ErrorCollector()); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals("1:3: Expected ARROW (->) but got IDENTIFIER (a).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadRuleWithProblemInLeft() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = OCocoParser.readRule("f(x y) -> f(x,y) rest", collector);
    assertTrue(rule.hasErrors());
    assertTrue(collector.queryCollectedMessages().toString().equals(
      "1:5: Expected a comma or closing bracket but got IDENTIFIER (y).\n" +
      "1:18: Expected end of input but got IDENTIFIER (rest).\n"));
  }

  @Test
  public void testReadRuleWithProblemInRight() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = OCocoParser.readRule("f(x,y) -> f(x y) rest", collector);
    assertTrue(rule.hasErrors());
    assertTrue(collector.queryCollectedMessages().toString().equals(
      "1:15: Expected a comma or closing bracket but got IDENTIFIER (y).\n" +
      "1:18: Expected end of input but got IDENTIFIER (rest).\n"));
  }

  @Test
  public void testReadRuleWithProblemInBoth() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = OCocoParser.readRule("f(x y) -> f(x y) rest", collector);
    assertTrue(rule.hasErrors());
    assertTrue(collector.queryCollectedMessages().toString().equals(
      "1:5: Expected a comma or closing bracket but got IDENTIFIER (y).\n" +
      "1:15: Expected a comma or closing bracket but got IDENTIFIER (y).\n" +
      "1:18: Expected end of input but got IDENTIFIER (rest).\n"));
  }

  // ===================================== reading a full TRS =====================================

  @Test
  public void testParseSimpleUnsortedTrs() {
    ParserProgram trs =
      OCocoParser.readProgramFromString("(VAR x y)\n" +
                                        "(RULES\n" +
                                        "  +(x, 0) -> x\n" +
                                        "  +(x, s(y)) -> s(+(x,y))\n" +
                                        ")");
    assertTrue(trs.fundecs().size() == 0);
    assertTrue(trs.rules().size() == 2);
    assertTrue(trs.rules().get(0).vars().size() == 2);
    assertTrue(trs.rules().get(0).vars().get("x").type().toString().equals("o"));
    assertTrue(trs.rules().get(0).vars().get("y").type().toString().equals("o"));
    assertTrue(trs.rules().get(0).toString().equals("{ [x, y] } @(+, [x, 0]) → x"));
    assertTrue(trs.rules().get(1).toString().equals(
      "{ [x, y] } @(+, [x, @(s, [y])]) → @(s, [@(+, [x, y])])"));
  }

  @Test
  public void testReadUnsortedTrsWithSignatureAndComment() {
    String str = "(VAR x ys xs)\n" +
                 "(SIG (nil 0) (cons 2) (append 2) (0 0) (s 1))\n" +
                 "(RULES\n" +
                 "  append(nil, zs) -> zs\n" +
                 "  append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n" +
                 ") (COMMENT hello world!)";
    ParserProgram trs = OCocoParser.readProgramFromString(str);
    assertTrue(trs.fundecs().size() == 5);
    assertTrue(trs.fundecs().get("0").type().toString().equals("o"));
    assertTrue(trs.fundecs().get("append").type().toString().equals("o → o → o"));
    assertTrue(trs.rules().size() == 2);
    assertTrue(trs.rules().get(0).toString().equals("{ [x, xs, ys] } @(append, [nil, zs]) → zs"));
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
    ParserProgram trs = OCocoParser.readProgramFromString(str);
    assertTrue(trs.fundecs().size() == 6);
    assertTrue(trs.fundecs().get("nil").type().toString().equals("List"));
    assertTrue(trs.rules().size() == 4);
    assertTrue(trs.rules().get(2).toString().equals("{ [] } @(len, [nil]) → 0"));
  }

  @Test
  public void testReadTrsWithMoreAfterEnding() {
    String str = "(VAR x y) (RULES f(x) -> y) uh oh!";
    try { OCocoParser.readProgramFromString(str); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:29: Expected end of input but got IDENTIFIER (uh).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadTrsWithMoreAfterComment() {
    String str = "(VAR x) (RULES f(x) -> g(x,)) (COMMENT extra comma ) there...) you see?";
    try { OCocoParser.readProgramFromString(str); }
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
    try { OCocoParser.readProgramFromString(str); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals("1:16: Unclosed comment.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testMixSigAndVar() {
    String str = "(SIG (f 2)) (VAR x) (RULES I can just type nonsense here";
    try { OCocoParser.readProgramFromString(str); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:13: Expected rules declaration but got VARSDECSTART ((VAR).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testMissingRules() {
    String str = "(SIG (f 2)) (COMMENT an empty file)";
    try { OCocoParser.readProgramFromString(str); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:13: Expected rules declaration but got COMMENTSTART ((COMMENT).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testRulesWithMissingBracketOnRight() {
    String str = "(SIG ) (RULES\n" +
      "f(x, s(y)) -> f(g(x),y\n" +
      "f(x,0) -> g(x)\n" +
      "0 -> 0)";
    ErrorCollector collector = new ErrorCollector();
    ParserProgram trs = OCocoParser.readProgramFromString(str, collector);
    assertTrue(collector.queryCollectedMessages().equals(
      "3:1: Expected a comma or closing bracket but got IDENTIFIER (f).\n" +
      "3:8: Expected a comma or closing bracket but got ARROW (->).\n"));
    assertTrue(trs.rules().size() == 2);
    assertTrue(trs.rules().get(0).left().toString().equals("@(f, [x, @(s, [y])])"));
    assertFalse(trs.rules().get(0).left().hasErrors());
    assertTrue(trs.rules().get(0).right().hasErrors());
    assertTrue(trs.rules().get(1).left().toString().equals("0"));
    assertFalse(trs.rules().get(1).left().hasErrors());
    assertFalse(trs.rules().get(1).right().hasErrors());
  }
}

