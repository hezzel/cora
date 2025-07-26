/**************************************************************************************************
 Copyright 2023-2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.parser;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.types.*;
import charlie.parser.lib.ParsingException;
import charlie.parser.lib.ErrorCollector;
import charlie.parser.lib.Token;
import charlie.parser.Parser.*;

public class CoraTrsParsingTest {
  @Test
  public void testEnvironmentWithJustVariables() {
    ParserRule rule = CoraParser.readRule("{ x :: Int, y :: b -> c } aa → aa");
    assertTrue(rule.constraint() == null);
    assertTrue(rule.left().toString().equals("aa"));
    assertTrue(rule.right().toString().equals("aa"));
    assertTrue(rule.vars().size() == 2);
    ParserDeclaration x = rule.vars().get("x");
    ParserDeclaration y = rule.vars().get("y");
    assertTrue(x.name().equals("x"));
    assertTrue(x.type().equals(TypeFactory.intSort));
    assertTrue(x.extra() == 0);
    assertTrue(y.name().equals("y"));
    assertTrue(y.type().toString().equals("b → c"));
    assertTrue(y.extra() == 0);
  }

  @Test
  public void testEnvironmentWithJustMetaVariables() {
    ParserRule rule = CoraParser.readRule("{ x ::[a,b] -> c,y :: [b] -> c, Z :: [] -> a } aa->aa");
    assertTrue(rule.vars().size() == 3);
    ParserDeclaration x = rule.vars().get("x");
    ParserDeclaration y = rule.vars().get("y");
    ParserDeclaration z = rule.vars().get("Z");
    assertTrue(x.type().toString().equals("a → b → c"));
    assertTrue(x.extra() == 2);
    assertTrue(y.type().toString().equals("b → c"));
    assertTrue(y.extra() == 1);
    assertTrue(z.type().toString().equals("a"));
    assertTrue(z.extra() == 0);
  }

  @Test
  public void testMixedEnvironment() {
    ParserRule rule = CoraParser.readRule("{ x :: a, y :: [b -> b,c] -> d -> e } aa → aa");
    assertTrue(rule.vars().size() == 2);
    ParserDeclaration x = rule.vars().get("x");
    ParserDeclaration y = rule.vars().get("y");
    ParserDeclaration z = rule.vars().get("Z");
    assertTrue(x.type().toString().equals("a"));
    assertTrue(x.extra() == 0);
    assertTrue(y.type().toString().equals("(b → b) → c → d → e"));
    assertTrue(y.extra() == 2);
    assertTrue(z == null);
  }

  @Test
  public void testEnvironmentWithDuplicateEntries() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = CoraParser.readRule(
      "{ x :: [a] → c , y :: c, x :: a → c, y :: [a] → d} aa → aa", false, collector);
    assertTrue(rule.vars().size() == 2);
    assertTrue(rule.vars().get("x").extra() == 1);
    assertTrue(rule.vars().get("y").type().toString().equals("c"));
    assertTrue(collector.toString().equals(
      "1:26: Redeclaration of variable x in the same environment.\n" +
      "1:38: Redeclaration of meta-variable y in the same environment.\n"));
  }

  @Test
  public void testEmptyEnvironment() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = CoraParser.readRule("{ }  aa → aa", false, collector);
    assertTrue(rule.toString().equals("{ [] } aa -> aa"));
    assertTrue(rule.vars().size() == 0);
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testForgotClosingBrace() {
    ErrorCollector col = new ErrorCollector();
    try { CoraParser.readRule("{ x :: a, y :: b -> c aa → aa\n { y :: a } next", true, col); }
    catch (ParsingException e) {
      assertTrue(e.getMessage().equals(
        "1:23: Expected comma or } but got IDENTIFIER (aa).\n" +
        // error recovery is done up to the next BRACEOPEN:
        "2:2: Expected end of input but got BRACEOPEN ({).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testPutRuleInsideEnvironment() {
    ErrorCollector col = new ErrorCollector();
    ParserRule rule =
      CoraParser.readRule("{ x :: [] -> a, y :: b -> c u → u, z :: d } bb -> bb", false, col);
    assertTrue(rule != null);
    assertTrue(rule.vars().get("x").type().toString().equals("a"));
    assertTrue(rule.vars().get("x").extra() == 0);
    assertTrue(rule.vars().get("y").type().toString().equals("b → c"));
    assertTrue(rule.vars().get("y").extra() == 0);
    assertTrue(rule.vars().get("z").type().toString().equals("d"));
    assertTrue(rule.vars().get("z").extra() == 0);
    assertTrue(rule.vars().size() == 3);
    assertTrue(col.toString().equals(
      "1:29: Expected comma or } but got IDENTIFIER (u).\n"));
  }

  @Test
  public void testPutHarmlessRuleAtEndOfEnvironment() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = CoraParser.readRule("{ x :: a, f(aa) -> aa } bb -> bb", true, collector);
    assertTrue(rule.vars().size() == 2);
    assertTrue(rule.vars().get("f").type().toString().equals("aa → aa"));
    assertTrue(rule.vars().get("f").extra() == 0);
    assertTrue(collector.toString().equals(
      "1:12: Expected declare symbol (::) but got BRACKETOPEN (().\n"));
  }

  @Test
  public void testStrayCommaAtEndOfEnvironment() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = CoraParser.readRule("{ x :: a, y :: b -> c, } aa → aa", false, collector);
    assertTrue(rule.vars().size() == 2);
    assertTrue(rule.vars().get("x").type().toString().equals("a"));
    assertTrue(rule.vars().get("y").type().toString().equals("b → c"));
    assertTrue(collector.toString().equals(
      "1:24: Expected a variable or meta-variable name but got BRACECLOSE (}).\n"));
  }

  @Test
  public void testEnvironmentWithUntypedVariable() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = CoraParser.readRule("{ x, y :: a } aa -> aa", true, collector);
    assertTrue(rule.vars().size() == 1);
    assertTrue(rule.vars().get("x") == null);
    assertTrue(rule.vars().get("y").type().toString().equals("a"));
    assertTrue(collector.toString().equals(
      "1:4: Expected declare symbol (::) but got COMMA (,).\n"));
  }

  @Test
  public void testEnvironmentWithIncompleteTypeDeclarationAtEnd() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = CoraParser.readRule("{ x :: [a } aa -> aa", false, collector);
    assertTrue(rule.vars().size() == 0);
    assertTrue(rule.toString().equals("{ [] } aa -> aa"));
    assertTrue(collector.toString().equals(
      "1:11: Expected comma or ] or ⟩ but got BRACECLOSE (}).\n"));
  }

  @Test
  public void testEnvironmentWithIncompleteTypeDeclarationInMiddle() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = CoraParser.readRule("{ x :: [a (), y :: Bool } aa -> aa", true, collector);
    assertTrue(rule.vars().size() == 0);
    assertTrue(rule.toString().equals("{ [] } aa -> aa"));
    assertTrue(collector.toString().equals(
      "1:11: Expected comma or ] or ⟩ but got BRACKETOPEN (().\n" +
      "1:12: Expected a type (started by a sort identifier or bracket) but got BRACKETCLOSE ()).\n" +
      "1:17: Expected comma or ] or ⟩ but got DECLARE (::).\n"));
  }

  @Test
  public void testEnvironmentWithCommalessMeta() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = CoraParser.readRule("{ x :: [a b] -> c } aa -> aa", true, collector);
    assertTrue(rule.vars().size() == 1);
    assertTrue(rule.vars().get("x").type().toString().equals("a → b → c"));
    assertTrue(rule.vars().get("x").extra() == 2);
    assertTrue(collector.toString().equals(
      "1:11: Expected comma or ] or ⟩ but got IDENTIFIER (b).\n"));
  }

  @Test
  public void testEnvironmentWithMetaDeclarationWithoutOutputType() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = CoraParser.readRule("{ x :: [b]}  aa -> aa", false, collector);
    assertTrue(rule.vars().size() == 0);
    assertTrue(rule.toString().equals("{ [] } aa -> aa"));
    assertTrue(collector.toString().equals(
      "1:11: Expected arrow operator -> but got BRACECLOSE (}).\n"));
  }

  @Test
  public void testEnvironmentWithIncorrectDeclares() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = CoraParser.readRule("{ x : a, y : b } aa -> aa", true, collector);
    assertTrue(rule.vars().size() == 0);
    assertTrue(rule.toString().equals("{ [] } aa -> aa"));
    assertTrue(collector.toString().equals(
      "1:5: Expected declare symbol (::) but got COLON (:).\n" +
      "1:12: Expected declare symbol (::) but got COLON (:).\n"));
  }

  @Test
  public void testCorrectFirstOrderRule() {
    ParserRule rule = CoraParser.readRule("h(x, y) -> h(x, h(aa, y))");
    assertTrue(rule.toString().equals("{ [] } @(h, [x, y]) -> @(h, [x, @(h, [aa, y])])"));
  }

  @Test
  public void testApplicativeRuleWithHeadVariable() {
    ParserRule rule = CoraParser.readRule("{ F :: a -> a } h(F(aa), bb) -> f(F(i(bb)))");
    assertTrue(rule.vars().size() == 1);
    assertTrue(rule.vars().get("F").type().toString().equals("a → a"));
    assertTrue(rule.vars().get("F").extra() == 0);
    assertTrue(rule.toString().equals(
      "{ [F] } @(h, [@(F, [aa]), bb]) -> @(f, [@(F, [@(i, [bb])])])"));
  }

  @Test
  public void testCreatePatternRule() {
    ParserRule rule = CoraParser.readRule("map(λx.F[x], cons(H, T)) → " +
                                          "cons(F[H], map(λx::nat.F[x], T))");
    assertTrue(rule.toString().equals("{ [] } @(map, [LAMBDA x.F[[x]], @(cons, [H, T])]) -> " +
      "@(cons, [F[[H]], @(map, [LAMBDA x::nat.F[[x]], T])])"));
  }

  @Test
  public void testCreateFirstOrderConstrainedRule() {
    ParserRule rule = CoraParser.readRule("sum(x) -> x + sum(x-1) | x > 0");
    assertTrue(rule.vars().size() == 0);
    assertTrue(rule.left().toString().equals("@(sum, [x])"));
    assertTrue(rule.right().toString().equals("@(+, [x, @(sum, [@(-, [x, 1])])])"));
    assertTrue(rule.constraint().toString().equals("@(>, [x, 0])"));
  }

  @Test
  public void testCreateHigherOrderConstrainedRule() {
    ParserRule rule = CoraParser.readRule("rec(F, x, y) → F(x, y, rec(F, x-1, y)) | x > 0");
    assertTrue(rule.toString().equals("{ [] } @(rec, [F, x, y]) -> " +
      "@(F, [x, y, @(rec, [F, @(-, [x, 1]), y])]) | @(>, [x, 0])"));
  }

  @Test
  public void testRuleWithComplexConstraint() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = CoraParser.readRule(
      "app(F,x) -> F(x)|0 <= x ∧ (x < 10 ∨ x = 13)\naa -> aa", true, collector);
    assertTrue(rule.toString().equals("{ [] } @(app, [F, x]) -> @(F, [x]) | " +
      "@(∧, [@(≤, [0, x]), @(∨, [@(<, [x, 10]), @(=, [x, 13])])])"));
    // we stop reading at the right point
    assertTrue(collector.toString().equals(
      "2:1: Expected end of input but got IDENTIFIER (aa).\n"));
  }

  @Test
  public void testRuleWithHigherVariableInConstraint() {
    ParserRule rule = CoraParser.readRule("filter(F,cons(H,T)) -> cons(H, filter(F, T)) | F(H)");
    // nothing wrong with this, no erorrs while parsing! (that happens in the reader)
    assertTrue(rule.toString().equals("{ [] } @(filter, [F, @(cons, [H, T])]) -> " +
      "@(cons, [H, @(filter, [F, T])]) | @(F, [H])"));
  }

  @Test
  public void testRuleWithBrokenLhs() {
    ErrorCollector collector = new ErrorCollector();
    try { CoraParser.readRule("() -> bb next x → x a b", false, collector); }
    catch (ParsingException e) {
      assertTrue(e.getMessage().equals("1:2: Expected term, started by " +
      "an identifier, LAMBDA, string or (, but got BRACKETCLOSE ()).\n" +
      // we do stop reading after bb
      "1:10: Expected end of input but got IDENTIFIER (next).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testRuleWithBrokenRhs() {
    try { CoraParser.readRule("aa -> () next aa :: bb", true, new ErrorCollector()); }
    catch (ParsingException e) {
      assertTrue(e.getMessage().equals("1:8: Expected term, started by an " +
        "identifier, LAMBDA, string or (, but got BRACKETCLOSE ()).\n" +
        "1:15: Expected end of input but got IDENTIFIER (aa).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testRuleWithMissingArrow() {
    try { CoraParser.readRule("{} aa bb cc", false, new ErrorCollector()); }
    catch (ParsingException e) {
      assertTrue(e.getMessage().equals(
        "1:7: Expected an arrow (→ or ->) but got IDENTIFIER (bb).\n"));
      // no further tokens are given, because error recovery takes us to the end of input
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testParseCorrectPublicDeclaration() {
    ErrorCollector collector = new ErrorCollector();
    ParserDeclaration decl =
      CoraParser.readDeclaration("public g :: a -> (b -> c) -> d\nx", false, collector);
    assertTrue(decl.name().equals("g"));
    assertTrue(decl.type().toString().equals("a → (b → c) → d"));
    assertTrue(decl.extra() == 0);
    // we stop readint at the right point
    assertTrue(collector.toString().equals(
      "2:1: Expected end of input but got IDENTIFIER (x).\n"));
  }

  @Test
  public void testParseCorrectPrivateDeclaration() {
    ErrorCollector collector = new ErrorCollector();
    ParserDeclaration decl =
      CoraParser.readDeclaration("private g :: a -> (b -> c) -> d\nx", false, collector);
    assertTrue(decl.name().equals("g"));
    assertTrue(decl.type().toString().equals("a → (b → c) → d"));
    assertTrue(decl.extra() == 1);
    // we stop readint at the right point
    assertTrue(collector.toString().equals(
      "2:1: Expected end of input but got IDENTIFIER (x).\n"));
  }

  @Test
  public void testParseCorrectDefaultDeclaration() {
    ErrorCollector collector = new ErrorCollector();
    ParserDeclaration decl =
      CoraParser.readDeclaration("g :: a -> (b -> c) -> d\nx", false, collector);
    assertTrue(decl.name().equals("g"));
    assertTrue(decl.type().toString().equals("a → (b → c) → d"));
    assertTrue(decl.extra() == 0);
    // we stop readint at the right point
    assertTrue(collector.toString().equals(
      "2:1: Expected end of input but got IDENTIFIER (x).\n"));
  }

  @Test
  public void testDoNotReadAnythingIfNotADeclaration() {
    ErrorCollector collector = new ErrorCollector();
    ParserDeclaration decl = CoraParser.readDeclaration("g(x,y)", true, collector);
    assertTrue(decl == null);
    assertTrue(collector.toString().equals(
      "1:1: Expected end of input but got IDENTIFIER (g).\n"));
  }

  @Test
  public void testRecoverAfterPublicNonDeclaration() {
    ErrorCollector collector = new ErrorCollector();
    ParserDeclaration decl = CoraParser.readDeclaration(
      "public g(x,y) -> x + y\naa :: bb\nc -> d", true, collector);
    assertTrue(decl != null);
    assertTrue(decl.type() == null);
    assertTrue(collector.toString().equals(
      "1:9: Expected :: but got BRACKETOPEN (().\n" +
      "2:1: Expected end of input but got IDENTIFIER (aa).\n"));
  }

  @Test
  public void testTryReadingDeclarationWithoutIdentifier() {
    ErrorCollector collector = new ErrorCollector();
    ParserDeclaration decl = CoraParser.readDeclaration(":: a -> b", false, collector);
    assertTrue(decl == null);
    assertTrue(collector.toString().equals(
      "1:1: Expected end of input but got DECLARE (::).\n"));
  }

  @Test
  public void testReadDefaultDeclarationFollowedByComma() {
    ErrorCollector collector = new ErrorCollector();
    ParserDeclaration decl = CoraParser.readDeclaration(
      "g :: a → (b -> c) , test\nhello\nf() -> d ->", true, collector);
    assertTrue(decl != null);
    assertTrue(decl.type() == null);
    assertTrue(collector.toString().equals(
      "3:10: Expected end of input but got ARROW (->).\n"));
    // we recognise that f() -> d is a rule, and continue after that
  }

  @Test
  public void testReadPublicDeclarationFollowedByComma() {
    ErrorCollector collector = new ErrorCollector();
    ParserDeclaration decl = CoraParser.readDeclaration(
      "public g :: a → (b -> c) , test\nhello\nf() -> d ->", false, collector);
    assertTrue(decl != null);
    assertTrue(decl.type() == null);
    assertTrue(collector.toString().equals(
      "1:26: Function symbol declartion cannot be followed by comma!\n" +
      "3:10: Expected end of input but got ARROW (->).\n"));
  }

  @Test
  public void testDeclarationWithIncorrectType() {
    ErrorCollector collector = new ErrorCollector();
    ParserDeclaration decl = CoraParser.readDeclaration(
      "g :: a -> (b -> ) → d", false, collector);
    assertTrue(decl != null);
    assertTrue(decl.type() != null);
    assertTrue(collector.toString().equals("1:17: Expected a type " +
      "(started by a sort identifier or bracket) but got BRACKETCLOSE ()).\n"));
  }

  @Test
  public void testDeclarationWithoutType() {
    ErrorCollector collector = new ErrorCollector();
    ParserDeclaration decl = CoraParser.readDeclaration("g :: {}", true, collector);
    assertTrue(decl != null);
    assertTrue(decl.type() == null);
    assertTrue(collector.toString().equals(
      "1:6: Expected a type (started by a sort identifier or bracket) but got BRACEOPEN ({).\n"));
  }

  @Test
  public void testDeclarationWithoutTypeFollowedByDot() {
    ErrorCollector collector = new ErrorCollector();
    ParserDeclaration decl =
      CoraParser.readDeclaration("private g :: . -> aλb {}", false, collector);
    assertTrue(decl != null);
    assertTrue(decl.type() == null);
    assertTrue(collector.toString().equals(
      "1:14: Expected a type (started by a sort identifier or bracket) but got DOT (.).\n" +
      "1:20: Expected end of input but got LAMBDA (λ).\n"));
  }

  @Test
  public void testDeclarationWithoutTypeFollowedByNonsense() {
    ErrorCollector collector = new ErrorCollector();
    ParserDeclaration decl =
      CoraParser.readDeclaration("g :: ) a λb aq :: b -> c next", true, collector);
    assertTrue(decl != null);
    assertTrue(decl.type() == null);
    assertTrue(collector.toString().equals(
      "1:6: Expected a type (started by a sort identifier or bracket) but got BRACKETCLOSE ()).\n" +
      "1:13: Expected end of input but got IDENTIFIER (aq).\n"));
  }

  @Test
  public void testShortFirstOrderProgram() {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram trs = CoraParser.readProgramFromString(
      "0 :: N s :: N -> N add :: N -> N -> N add(0,y) -> y add(s(x),y) -> s(add(x,y))",
      false, collector);
    assertTrue(trs.fundecs().size() == 3);
    assertTrue(trs.fundecs().get("0").type().toString().equals("N"));
    assertTrue(trs.fundecs().get("s").type().toString().equals("N → N"));
    assertTrue(trs.fundecs().get("add").type().toString().equals("N → N → N"));
    assertTrue(trs.rules().get(0).toString().equals("{ [] } @(add, [0, y]) -> y"));
    assertTrue(trs.rules().get(1).toString().equals(
      "{ [] } @(add, [@(s, [x]), y]) -> @(s, [@(add, [x, y])])"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testWeirdProgram() {
    ParserProgram trs =
      CoraParser.readProgramFromString("f(x,x) -> x f :: a -> a -> a b :: b b -> b c :: a");
    assertTrue(trs.fundecs().get("f").type().toString().equals("a → a → a"));
    assertTrue(trs.fundecs().get("b").type().toString().equals("b"));
    assertTrue(trs.fundecs().get("c").type().toString().equals("a"));
    assertTrue(trs.rules().get(0).toString().equals("{ [] } @(f, [x, x]) -> x"));
    assertTrue(trs.rules().get(1).toString().equals("{ [] } b -> b"));
  }

  @Test
  public void testErrorneousDeclaration() {
    try {
      ParserProgram trs = CoraParser.readProgramFromString("f :: a -> a -> b :: c d :: e");
    }
    catch(ParsingException e) {
      assertTrue(e.getMessage().equals("1:18: Expected term, started by an identifier, LAMBDA, " +
        "string or (, but got DECLARE (::).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testMultipleErrorsWithConstrainedRules() {
    try {
      ParserProgram trs = CoraParser.readProgramFromString(
        "f :: Int -> Int\n" +
        "f(x) -> f(x + 2 | x < 0 \n" +
        "f(x) -> x | x > 0)\n" +
        "f(2) -> 3\n" +
        "- :: Int -> Int -> Int\n" +
        "f(3) -> 4 | true \n" +
        "-(x, y) -> x + -1 * y\n");
    }
    catch (ParsingException e) {
      assertTrue(e.getMessage().equals(
        "2:17: Expected a comma or closing bracket ) but got MID (|).\n" +
        "3:18: Expected term, started by an identifier, LAMBDA, string or (, but got " +
          "BRACKETCLOSE ()).\n" +
        "5:3: Expected term, started by an identifier, LAMBDA, string or (, but got " +
          "DECLARE (::).\n" +
        "7:4: Expected a closing bracket but got COMMA (,).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testDisallowDuplicateDeclarations() {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram trs = CoraParser.readProgramFromString(
        "a :: aa b :: bb a :: aa b :: bb -> aa", true, collector);
    assertTrue(trs.fundecs().size() == 2);
    assertTrue(trs.fundecs().get("a").type().toString().equals("aa"));
    assertTrue(trs.fundecs().get("b").type().toString().equals("bb"));
    assertTrue(collector.toString().equals(
      "1:17: Redeclaration of previously declared function symbol a.\n" +
      "1:25: Redeclaration of previously declared function symbol b.\n"));
  }
}

