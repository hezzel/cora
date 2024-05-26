/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

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
import com.google.common.collect.ImmutableList;

import charlie.types.*;
import charlie.parser.lib.ErrorCollector;
import charlie.parser.lib.Token;
import charlie.parser.Parser.*;

public class CoraTermsParsingTest {
  /**
   * Helper function: this reads the term from txt, and verifies that the corresponding error
   * message is exactly message (use "" if there should not be any errors), and returns the
   * result.
   */
  private ParserTerm readTerm(String txt, boolean constrained, String message) {
    ErrorCollector collector = new ErrorCollector();
    ParserTerm ret = CoraParser.readTerm(txt, constrained, collector);
    if (!collector.queryCollectedMessages().equals(message)) {
      System.out.println(collector.queryCollectedMessages());
      System.out.println("ret = " + ret);
      assertTrue(false);
    }
    return ret;
  }

  @Test
  public void testStringsNotAllowedInUnconstrainedTerms() {
    ParserTerm t = readTerm("\"hi!\"", false,
      "1:1: String constants are only allowed in constrained systems.\n");
    assertTrue(t.toString().equals("\"hi!\""));
  }

  @Test
  public void testReadSingleString() {
    ParserTerm term = readTerm("\"hello world!\\n\"", true, "");
    assertTrue(term instanceof StringVal);
    assertTrue(term.toString().equals("\"hello world!\\n\""));
  }

  @Test
  public void testReadMultipleStrings() {
    ParserTerm term = readTerm("\"hello\"\n \" world!\"", true, "");
    assertTrue(term instanceof StringVal);
    assertTrue(term.toString().equals("\"hello world!\""));
  }

  @Test
  public void testMoreThanAString() {
    ParserTerm term = readTerm("\"a\"b", true,
      "1:4: Expected end of input but got IDENTIFIER (b).\n");
    assertTrue(term instanceof StringVal);
    assertTrue(term.toString().equals("\"a\""));
  }

  @Test
  public void testReadNonNegativeIntegers() {
    ParserTerm term = readTerm("12", true, "");
    assertTrue(term instanceof IntVal);
    assertTrue(term.toString().equals("12"));
    term = readTerm("0", true, "");
    assertTrue(term instanceof IntVal);
    assertTrue(term.toString().equals("0"));
  }

  @Test
  public void testReadNegativeIntegers() {
    ParserTerm term = readTerm("- 37", true, "");
    assertTrue(term instanceof IntVal);
    assertTrue(term.toString().equals("-37"));
    term = readTerm("-1", true, "");
    assertTrue(term instanceof IntVal);
    assertTrue(term.toString().equals("-1"));
  }

  @Test
  public void testIllegalIntegers() {
    ParserTerm term = readTerm("0000", true, "1:1: Illegal integer constant: 0000.\n");
    assertTrue(term instanceof IntVal);
    assertTrue(term.toString().equals("0"));
    term = readTerm("017", true, "1:1: Illegal integer constant: 017.\n");
    assertTrue(term instanceof IntVal);
    assertTrue(term.toString().equals("17"));
    term = readTerm("123456789123456789", true,
      "1:1: Cannot parse integer constant: 123456789123456789\n");
    assertTrue(term instanceof Identifier);
    assertTrue(term.toString().equals("123456789123456789"));
  }

  @Test
  public void testReadUnconstrainedIntegers() {
    ParserTerm term = readTerm("0000", false, "");
    assertTrue(term instanceof Identifier);
    assertTrue(term.toString().equals("0000"));
    term = readTerm("37", false, "");
    assertTrue(term instanceof Identifier);
    assertTrue(term.toString().equals("37"));
    term = readTerm("-19", false, "");
    assertTrue(term instanceof Identifier);
    assertTrue(term.toString().equals("-19"));
    term = readTerm("- 3", false, "1:3: Expected end of input but got IDENTIFIER (3).\n");
    assertTrue(term instanceof Identifier);
    assertTrue(term.toString().equals("-"));
  }

  @Test
  public void testReadBooleans() {
    ParserTerm term = readTerm("true", true, "");
    assertTrue(term instanceof BoolVal);
    assertTrue(term.toString().equals("⊤"));
    term = readTerm("false", true, "");
    assertTrue(term instanceof BoolVal);
    assertTrue(term.toString().equals("⊥"));
    term = readTerm("FALSE", true, "");
    assertTrue(term instanceof Identifier);
    assertTrue(term.toString().equals("FALSE"));
    term = readTerm("true", false, "");
    assertTrue(term instanceof Identifier);
    assertTrue(term.toString().equals("true"));
  }

  @Test
  public void testReadIdentifier() {
    ParserTerm t = readTerm("xx_y∀y", false, "");
    assertTrue(t instanceof Identifier);
    assertTrue(t.toString().equals("xx_y∀y"));
  }

  @Test
  public void testReadEmptyApplication() {
    ParserTerm t = readTerm("bb()", true, "");
    if (t instanceof Application(Token token, ParserTerm head, ImmutableList args)) {
      assertTrue(head instanceof Identifier);
      assertTrue(head.toString().equals("bb"));
      assertTrue(args.size() == 0);
    }
    else assertTrue(false);
  }

  @Test
  public void testReadFullApplication() {
    ParserTerm t = readTerm("f(aa,bb,cc)", false, "");
    if (t instanceof Application(Token token, ParserTerm head, ImmutableList args)) {
      assertTrue(head instanceof Identifier);
      assertTrue(head.toString().equals("f"));
      assertTrue(args.size() == 3);
      assertTrue(args.get(0) instanceof Identifier);
      assertTrue(args.get(1) instanceof Identifier);
      assertTrue(args.get(2) instanceof Identifier);
      assertTrue(args.get(0).toString().equals("aa"));
      assertTrue(args.get(1).toString().equals("bb"));
      assertTrue(args.get(2).toString().equals("cc"));
    }
    else assertTrue(false);
  }

  @Test
  public void testNestedFunctionalTerm() {
    ParserTerm t = readTerm("f(x,h(f(x, a)),cc)", true, "");
    assertTrue(t.toString().equals("@(f, [x, @(h, [@(f, [x, a])]), cc])"));
  }

  @Test
  public void testTermWithValues() {
    ParserTerm t = readTerm("new(3,true,\"test\" \"ing\",aa)", true, "");
    if (!(t instanceof Application(Token tok, ParserTerm head, ImmutableList<ParserTerm> args))) {
      assertTrue(false);
      return;
    }
    assertTrue(head instanceof Identifier);
    assertTrue(head.toString().equals("new"));
    assertTrue(args.size() == 4);
    assertTrue(args.get(0) instanceof IntVal);
    assertTrue(args.get(1) instanceof BoolVal);
    assertTrue(args.get(2) instanceof StringVal);
    assertTrue(args.get(3) instanceof Identifier);
    assertTrue(t.toString().equals("@(new, [3, ⊤, \"testing\", aa])"));
  }

  @Test
  public void testRepeatedApplication() {
    ParserTerm t = readTerm("f(aa)(x,cc)", false, "");
    assertTrue(t.toString().equals("@(@(f, [aa]), [x, cc])"));
  }

  @Test
  public void testValueAtHead() {
    ParserTerm t = readTerm("12(aa)", true, "");
    assertTrue(t.toString().equals("@(12, [aa])"));
  }

  @Test
  public void testMissingBracket() {
    ParserTerm t = readTerm("f(x,h(f(x, bb),cc)", true,
      "1:19: Expected a comma or closing bracket ) but got end of input.\n");
    assertTrue(t.toString().equals("@(f, [x, ERR(@(h, [@(f, [x, bb]), cc]))])"));
  }

  @Test
  public void testDuplicateComma() {
    ParserTerm t = readTerm("f(x,,y)", false,
      "1:5: Unexpected comma; expected term or closing bracket )\n");
    assertTrue(t.toString().equals("@(f, [x, ERR(y)])"));
  }

  @Test
  public void testOnlyCommas() {
    ParserTerm t = readTerm("f(,,,)", false,
      "1:3: Unexpected comma; expected term or closing bracket )\n" +
      "1:6: Expected term, started by an identifier, λ, string or (, but got BRACKETCLOSE ()).\n");
    assertTrue(t.toString().equals("ERR(f)"));
  }

  @Test
  public void testMissingComma() {
    ParserTerm t = readTerm("f(x,h(f(x, bb)) cc)", true,
      "1:17: Expected a comma or closing bracket ) but got IDENTIFIER (cc).\n");
    assertTrue(t.toString().equals("@(f, [x, @(h, [@(f, [x, bb])]), ERR(cc)])"));
  }

  @Test
  public void testReadBasicAbstractionWithType() {
    ParserTerm t = readTerm("λx :: a. f(x, bb, y)", false, "");
    assertTrue(t.toString().equals("λx::a.@(f, [x, bb, y])"));
  }

  @Test
  public void testReadBasicAbstractionWithoutType() {
    ParserTerm t = readTerm("λx. f(x, bb, y)", false, "");
    assertTrue(t.toString().equals("λx.@(f, [x, bb, y])"));
  }

  @Test
  public void testReadMultipleAbstractionWithBinderDeclarations() {
    ParserTerm t = readTerm("λx :: a, y ::c. f(x, bb, y)", true, "");
    assertTrue(t.toString().equals("λx::a.λy::c.@(f, [x, bb, y])"));
  }

  @Test
  public void testReadMultipleAbstractionWithoutBinderDeclaration() {
    ParserTerm t = readTerm("h(\\x,z.f(aa,bb,x))", true, "");
    assertTrue(t.toString().equals("@(h, [λx.λz.@(f, [aa, bb, x])])"));
  }

  @Test
  public void testReadAbstractionWithDuplicateVariableName() {
    ParserTerm t = readTerm("λx::a, y, x.x", false, "");
    assertTrue(t.toString().equals("λx::a.λy.λx.x"));
  }

  @Test
  public void testReadAbstractionAtHeadOfApplication() {
    ParserTerm t = readTerm("(λx :: a, y ::c. f(x,bb,y))(aa,cc)", false, "");
    assertTrue(t.toString().equals("@(λx::a.λy::c.@(f, [x, bb, y]), [aa, cc])"));
  }

  @Test
  public void testReadAbstractionWithBrokenType() {
    ParserTerm t = readTerm("λx :: a -> .x y", false,
      "1:12: Expected a type (started by a sort identifier or bracket) but got DOT (.).\n" +
      "1:15: Expected end of input but got IDENTIFIER (y).\n");
    assertTrue(t.toString().equals("λx::a.x"));
  }

  @Test
  public void testReadAbstractionWithMissingType() {
    ParserTerm t = readTerm("λx :: .x y", true,
      "1:7: Expected a type (started by a sort identifier or bracket) but got DOT (.).\n" +
      "1:10: Expected end of input but got IDENTIFIER (y).\n");
    assertTrue(t.toString().equals("ERR(λx.x)"));
  }

  @Test
  public void testReadMultipleAbstractionWithMissingComma() {
    ParserTerm t = readTerm("\\x :: a y.f(x,y,cc)", false,
      "1:9: Expected a comma or dot but got IDENTIFIER (y).\n");
    assertTrue(t.toString().equals("λx::a.λy.@(f, [x, y, cc])"));
  }

  @Test
  public void testCompletelyDifferentTokenInAbstractionList() {
    ParserTerm t = readTerm("\\x \"test\".aa", true,
      "1:4: Expected a comma or dot but got STRING (\"test\").\n" +
      "1:10: Expected end of input but got DOT (.).\n");
    assertTrue(t.toString().equals("ERR(λx.\"test\")"));
  }

  @Test
  public void testMissingBinderName() {
    ParserTerm t = readTerm("λ :: a, x :: b.x", true,
      "1:3: Expected an identifier (variable name) but got DECLARE (::).\n");
    assertTrue(t.toString().equals("ERR(λx::b.x)"));
  }

  @Test
  public void testExtraCommaInAbstractionBinders() {
    ParserTerm t = readTerm("λ x, .aa", true,
      "1:6: Expected an identifier (variable name) but got DOT (.).\n");
    assertTrue(t.toString().equals("ERR(λx.aa)"));
  }

  @Test
  public void testMetaVariableWithEmptyArgumentsList() {
    ParserTerm t = readTerm("Z[]", false, "");
    if (t instanceof Meta(Token token, String name, ImmutableList<ParserTerm> args)) {
      assertTrue(name.equals("Z"));
      assertTrue(args.size() == 0);
    }
    else assertTrue(false);
  }

  @Test
  public void testMetaApplicationWithOneArgument() {
    ParserTerm t = readTerm("Z⟨x⟩", false, "");
    if (t instanceof Meta(Token token, String name, ImmutableList<ParserTerm> args)) {
      assertTrue(name.equals("Z"));
      assertTrue(args.size() == 1);
      assertTrue(args.get(0) instanceof Identifier);
      assertTrue(args.get(0).toString().equals("x"));
    }
    else assertTrue(false);
  }

  @Test
  public void testMetaApplicationWithMixedBrackets() {
    ParserTerm t = readTerm("Z⟨x,3]", true, "");
    if (t instanceof Meta(Token token, String name, ImmutableList<ParserTerm> args)) {
      assertTrue(name.equals("Z"));
      assertTrue(args.size() == 2);
      assertTrue(args.get(0) instanceof Identifier);
      assertTrue(args.get(0).toString().equals("x"));
      assertTrue(args.get(1) instanceof IntVal);
      assertTrue(args.get(1).toString().equals("3"));
    }
    else assertTrue(false);
  }

  @Test
  public void testReadNestedMeta() {
    ParserTerm t = readTerm("Z⟨aa,Y[x⟩,cc]", false, "");
    if (t instanceof Meta(Token token, String name, ImmutableList<ParserTerm> args)) {
      assertTrue(name.equals("Z"));
      assertTrue(args.size() == 3);
      assertTrue(args.get(0) instanceof Identifier);
      assertTrue(args.get(1) instanceof Meta);
      assertTrue(args.get(2) instanceof Identifier);
      assertTrue(args.get(1).toString().equals("Y⟨[x]⟩"));
    }
    else assertTrue(false);
  }

  @Test
  public void testAppliedMetaApplication() {
    ParserTerm t = readTerm("Z⟨aa⟩(bb,cc)", true, "");
    assertTrue(t.toString().equals("@(Z⟨[aa]⟩, [bb, cc])"));
  }

  @Test
  public void testMetaApplicationWithExtraComma() {
    ParserTerm t = readTerm("Z[aa,,bb]",  true,
      "1:6: Unexpected comma; expected term or meta-closing bracket ]\n");
    assertTrue(t.toString().equals("Z⟨[aa, ERR(bb)]⟩"));
  }

  @Test
  public void testMetaApplicationWithMissingCommas() {
    ParserTerm t = readTerm("Z[aa bb cc]", false,
      "1:6: Expected a comma or meta-closing bracket ] but got IDENTIFIER (bb).\n" +
      "1:9: Expected a comma or meta-closing bracket ] but got IDENTIFIER (cc).\n");
    assertTrue(t.toString().equals("Z⟨[aa, ERR(bb), ERR(cc)]⟩"));
  }

  @Test
  public void testMissingCloseBracket() {
    ParserTerm t = readTerm("Z⟨aa,x}", true,
      "1:7: Expected a comma or meta-closing bracket ⟩ but got BRACECLOSE (}).\n");
    assertTrue(t.toString().equals("Z⟨[aa, ERR(x)]⟩"));
  }

  @Test
  public void testReadSimpleInfix() {
    ParserTerm t = readTerm("1+2", true, "");
    if (t instanceof Application(Token t1, CalcSymbol(Token t2, String name),
                                 ImmutableList<ParserTerm> args)) {
      assertTrue(name.equals("+"));
      assertTrue(args.size() == 2);
      assertTrue(args.get(0) instanceof IntVal);
      assertTrue(args.get(1) instanceof IntVal);
      assertTrue(t.toString().equals("@(+, [1, 2])"));
    }
    else assertTrue(false);
  }

  @Test
  public void testReadInfixWithLeftToRightPriority() {
    ParserTerm t = readTerm("1*2+3 > x", true, "");
    assertTrue(t.toString().equals("@(>, [@(+, [@(*, [1, 2]), 3]), x])"));
  }

  @Test
  public void testReadInfixWithRightToLeftPriority() {
    ParserTerm t = readTerm("x >= 3 + y * 2", true, "");
    assertTrue(t.toString().equals("@(≥, [x, @(+, [3, @(*, [y, 2])])])"));
  }

  @Test
  public void testReadSimpleNot() {
    ParserTerm t = readTerm("¬x", true, "");
    if (t instanceof Application(Token t1, CalcSymbol(Token t2, String name),
                                 ImmutableList<ParserTerm> args)) {
      assertTrue(name.equals("¬"));
      assertTrue(args.size() == 1);
      assertTrue(args.get(0) instanceof Identifier);
      assertTrue(args.get(0).toString().equals("x"));
    }
    else assertTrue(false);
  }

  @Test
  public void testMostlySimpleMinus() {
    ParserTerm t = readTerm("- (3+x)", true, "");
    assertTrue(t instanceof Application(Token tok, CalcSymbol m, ImmutableList<ParserTerm> args));
    assertTrue(t.toString().equals("@(-, [@(+, [3, x])])"));
  }

  @Test
  public void testDuplicateNot() {
    ParserTerm t = readTerm("¬¬ ( x > 0)", true, "");
    assertTrue(t.toString().equals("@(¬, [@(¬, [@(>, [x, 0])])])"));
  }

  @Test
  public void testBracketOmissionForNot() {
    ParserTerm t = readTerm("¬ x > 0", true, "");
    assertTrue(t.toString().equals("@(>, [@(¬, [x]), 0])"));
  }

  @Test
  public void testMinusBeforeAddition() {
    ParserTerm t = readTerm("- x + y", true, "");
    assertTrue(t.toString().equals("@(+, [@(-, [x]), y])"));
  }

  @Test
  public void testNegativeIntegerInMultiplication() {
    ParserTerm t = readTerm("-2*1", true, "");
    assertTrue(t.toString().equals("@(*, [-2, 1])"));
  }

  @Test
  public void testReadSimpleMinusWithIdentifier() {
    ParserTerm t = readTerm("x - y", true, "");
    assertTrue(t.toString().equals("@(-, [x, y])"));
  }

  @Test
  public void testReadSimpleMinusWithConstant() {
    ParserTerm t = readTerm("x - 3", true, "");
    assertTrue(t.toString().equals("@(-, [x, 3])"));
  }

  @Test
  public void testReadComplexMinuses() {
    ParserTerm t = readTerm("x -3 % 5 + 1 < -1-y", true, "");
    assertTrue(t.toString().equals("@(<, [@(+, [@(-, [x, @(%, [3, 5])]), 1]), @(-, [-1, y])])"));
  }

  @Test
  public void testMixedInfixPriorities() {
    ParserTerm t = readTerm("q(x) < y /\\ y / 2 > Z[aa] + -13 * z +9", true, "");
    assertTrue(t.toString().equals("@(∧, [@(<, [@(q, [x]), y]), " +
      "@(>, [@(/, [y, 2]), @(+, [@(+, [Z⟨[aa]⟩, @(*, [-13, z])]), 9])])])"));
  }

  @Test
  public void testDoublePlus() {
    ParserTerm t = readTerm("1 ++2", true,
      "1:4: Expected term, started by an identifier, λ, string or (, but got PLUS (+).\n");
    assertTrue(t.toString().equals("ERR(1)"));
  }

  @Test
  public void testPrefix() {
    ParserTerm t = readTerm("[-]", true, "");
    assertTrue(t instanceof CalcSymbol(Token token, String name));
    assertTrue(t.toString().equals("-"));
    t = readTerm("⟨+⟩(2)", true, "");
    assertTrue(t instanceof Application(Token t1, CalcSymbol(Token t2, String name),
                                        ImmutableList<ParserTerm> args));
    assertTrue(t.toString().equals("@(+, [2])"));
    t = readTerm("⟨/⟩(2, x, 9)", true, "");
    assertTrue(t.toString().equals("@(/, [2, x, 9])"));
    t = readTerm("[¬]", true, "");
    assertTrue(t.toString().equals("¬"));
    t = readTerm("[¬](7)", true, "");
    assertTrue(t.toString().equals("@(¬, [7])"));
  }

  @Test
  public void testBadPrefix() {
    ParserTerm t = readTerm("[$]", true, "1:2: Expected infix symbol but got IDENTIFIER ($)\n");
    assertTrue(t.toString().equals("ERR($)"));
  }

  @Test
  public void testReadGoodTuple() {
    ParserTerm t = readTerm("⦇ a, x, f(2) ⦈", false, "");
    assertTrue(t instanceof Tup);
    assertTrue(t.toString().equals("⦇[a, x, @(f, [2])]⦈"));
  }

  @Test
  public void testReadEmptyTuple() {
    ParserTerm t = readTerm("⦇ ⦈", true, "1:1: Empty tuples are not allowed.\n");
    assertTrue(t.toString().equals("ERR(⦇⦈)"));
  }

  @Test
  public void testReadSingularTuple() {
    ParserTerm t = readTerm("⦇ f(a) ⦈", true,
      "1:1: Tuples of length 1 are not allowed.\n");
    assertTrue(t.toString().equals("@(f, [a])"));
  }

  @Test
  public void testReadTupleWithoutClosingBracket() {
    ParserTerm t = readTerm("⦇x, 1 { a, b } f -> f", true,
      "1:7: Expected a comma or tuple closing bracket ⦈ but got BRACEOPEN ({).\n");
    assertTrue(t.toString().equals("⦇[x, ERR(1)]⦈"));
  }

  @Test
  public void testMissingCommaInTuple() {
    ParserTerm t = readTerm("⦇x y⦈ -> x", false,
      "1:4: Expected a comma or tuple closing bracket ⦈ but got IDENTIFIER (y).\n" +
      "1:7: Expected end of input but got ARROW (->).\n");
    assertTrue(t.toString().equals("⦇[x, ERR(y)]⦈"));
  }
}

