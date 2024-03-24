/**************************************************************************************************
 Copyright 2019--2024 Cynthia Kop

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

import charlie.exceptions.ParseError;
import charlie.util.LookupMap;
import charlie.parser.lib.ErrorCollector;
import charlie.parser.Parser.*;

public class ITrsParserTest {
  @Test
  public void testReadCorrectVarList() {
    ParserProgram prog = ITrsParser.readProgramFromString("(VAR x y) (RULES a ->b b -> a)");
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
  public void testReadIntegerValue() {
    ParserTerm term = ITrsParser.readTerm("12");
    assertTrue(term instanceof IntVal);
    assertTrue(term.toString().equals("12"));
    term = ITrsParser.readTerm("0009");
    assertTrue(term instanceof IntVal);
    assertTrue(term.toString().equals("9"));
  }

  @Test
  public void testReadBooleanValue() {
    ParserTerm term = ITrsParser.readTerm("TRUE");
    assertTrue(term instanceof BoolVal);
    assertTrue(term.toString().equals("⊤"));
    term = ITrsParser.readTerm("FALSE");
    assertTrue(term instanceof BoolVal);
    assertTrue(term.toString().equals("⊥"));
  }

  @Test
  public void testReadIdentifier() {
    ParserTerm term = ITrsParser.readTerm("12x");
    assertTrue(term instanceof Identifier);
    assertTrue(term.toString().equals("12x"));
  }

  @Test
  public void testReadSimpleFunctionalTerm() {
    ParserTerm term = ITrsParser.readTerm("f(x1, g(y), z)");
    assertTrue(term instanceof Application);
    assertTrue(term.toString().equals("@(f, [x1, @(g, [y]), z])"));
  }

  @Test
  public void testReadAddition() {
    ParserTerm term = ITrsParser.readTerm("x + 3");
    assertTrue(term instanceof Application);
    assertTrue(term.toString().equals("@(+, [x, 3])"));
  }

  @Test
  public void testReadPrefix() {
    ParserTerm term = ITrsParser.readTerm("-12");
    assertTrue(term instanceof Application);
    assertTrue(term.toString().equals("@(-, [12])"));
    term = ITrsParser.readTerm("! x");
    assertTrue(term instanceof Application);
    assertTrue(term.toString().equals("@(not, [x])"));
  }

  @Test
  public void testBracketedTerm() {
    ParserTerm term = ITrsParser.readTerm("(x * y % z)");
    assertTrue(term instanceof Application);
    assertTrue(term.toString().equals("@(%, [@(*, [x, y]), z])"));
    term = ITrsParser.readTerm("x * (y % z)");
    assertTrue(term.toString().equals("@(*, [x, @(%, [y, z])])"));
  }

  @Test
  public void testReadComplexConstraint() {
    ParserTerm term = ITrsParser.readTerm("a + (b - 12 * x) >= 4 * x && 14 > - y");
    assertTrue(term.toString().equals(
      "@(∧, [@(≥, [@(+, [a, @(-, [b, @(*, [12, x])])]), @(*, [4, x])]), @(>, [14, @(-, [y])])])"));
  }

  @Test
  public void testReadMissingCloseBracket() {
    ErrorCollector collector = new ErrorCollector();
    ParserTerm term = ITrsParser.readTerm("f(a, b(x)", collector);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:10: Expected a comma or closing bracket but got end of input.\n"));
    assertTrue(term.hasErrors());
    assertTrue(term.toString().equals("ERR(@(f, [a, @(b, [x])]))"));
  }

  @Test
  public void testReadEmptyBracketList() {
    ParserTerm term = ITrsParser.readTerm("x()");
    assertFalse(term.hasErrors());
    assertTrue(term instanceof Parser.Application);
    assertTrue(term.toString().equals("@(x, [])"));
  }

  @Test
  public void testReadComplexTerm() {
    ErrorCollector collector = new ErrorCollector();
    ParserTerm term = ITrsParser.readTerm("f(g(x, y), h(x, u(), g(a, y)))", collector);
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(term.toString().equals("@(f, [@(g, [x, y]), @(h, [x, @(u, []), @(g, [a, y])])])"));
  }

  @Test
  public void testReadTermWithMultipleInconsistencies() {
    ErrorCollector collector = new ErrorCollector();
    ParserTerm term = ITrsParser.readTerm("f(a, a(, x), g(y, ), a(b)", collector);
    assertTrue(collector.queryErrorCount() == 3);
    assertTrue(collector.queryCollectedMessages().equals(
        "1:8: Expected an identifier (variable or function name) but got COMMA (,).\n" +
        "1:19: Expected an identifier (variable or function name) but got BRACKETCLOSE ()).\n" +
        "1:26: Expected a comma or closing bracket but got end of input.\n"));
    assertTrue(term.toString().equals("ERR(@(f, [a, ERR(@(a, [x])), ERR(@(g, [y])), @(a, [b])]))"));
  }

  @Test
  public void testReadUnconstrainedCorrectRule() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = ITrsParser.readRule("f(x,s(y)) -> f(s(x + 1), y)", collector);
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(rule.toString().equals(
      "{ [] } @(f, [x, @(s, [y])]) → @(f, [@(s, [@(+, [x, 1])]), y])"));
  }

  @Test
  public void testReadAmbiguousTerm() {
    ErrorCollector collector = new ErrorCollector();
    ParserTerm term = ITrsParser.readTerm("x && y || z", collector);
    assertTrue(collector.queryCollectedMessages().equals(
      "1:8: Ambiguous infix sequence: operators && (at position 1:3) and || " +
      "have the same precedence, but are not in the same group.  Please use " +
      "brackets to disambiguate.\n"));
    assertTrue(term.toString().equals("@(∨, [ERR(@(∧, [x, y])), z])"));
  }

  @Test
  public void testReadConstrainedCorrectRule() {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = ITrsParser.readRule("f(x,y) -> g(x / y) :|: y > 0", collector);
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(rule.toString().equals("{ [] } @(f, [x, y]) → @(g, [@(/, [x, y])]) | @(>, [y, 0])"));
  }

  @Test
  public void testParseSimpleUnconstrainedTrs() {
    ParserProgram trs =
      ITrsParser.readProgramFromString("(VAR x y)\n" +
                                       "(RULES\n" +
                                       "  f(x, y, TRUE) -> f(y + x, 12, FALSE)\n" +
                                       "  f(x, y, FALSE) -> end\n" +
                                       ")");
    assertTrue(trs.fundecs().size() == 0);
    assertTrue(trs.rules().size() == 2);
    assertTrue(trs.rules().get(0).vars().size() == 2);
    assertTrue(trs.rules().get(0).toString().equals("{ [x, y] } @(f, [x, y, ⊤]) → " +
      "@(f, [@(+, [y, x]), 12, ⊥])"));
  }

  @Test
  public void testSimpleConsttrainedTrs() {
    ParserProgram trs =
      ITrsParser.readProgramFromString("(VAR x)\n" +
                                       "(RULES\n" +
                                       "  sum(x) -> x + sum(x-1) :|: x > 0\n" +
                                       "  sum(0) -> 0\n" +
                                       "  sum(x) -> -1 :|: x < 0\n" +
                                       ")\n" +
                                       "(COMMENT a -> b)");
    assertTrue(trs.fundecs().size() == 0);
    assertTrue(trs.rules().size() == 3);
    assertTrue(trs.rules().get(0).vars().size() == 1);
    assertTrue(trs.rules().get(0).toString().equals(
      "{ [x] } @(sum, [x]) → @(+, [x, @(sum, [@(-, [x, 1])])]) | @(>, [x, 0])"));
    assertTrue(trs.rules().get(1).toString().equals(
      "{ [x] } @(sum, [0]) → 0"));
    assertTrue(trs.rules().get(2).toString().equals(
      "{ [x] } @(sum, [x]) → @(-, [1]) | @(<, [x, 0])"));
  }

  @Test
  public void testMissingRules() {
    String str = "(VAR x y) (COMMENT an empty file)";
    try { ITrsParser.readProgramFromString(str); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:11: Expected rules declaration but got COMMENTSTART ((COMMENT).\n"));
      return;
    }
    assertTrue(false);
  }
}

