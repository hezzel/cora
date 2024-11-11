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

import java.util.TreeSet;

import charlie.parser.lib.Token;
import charlie.parser.lib.LexerException;
import charlie.parser.lib.Lexer;

public class CoraConstrainedTokensTest {
  private TreeSet<String> errors;

  private Lexer createLexer(String str) {
    errors = new TreeSet<String>();
    return CoraTokenData.getConstrainedStringLexer(str);
  }

  private void verifyToken(Token tk, String name, String text) {
    assertTrue(tk.getName().equals(name));
    assertTrue(tk.getText().equals(text));
  }

  private boolean checkExceptionOnNextToken(Lexer lexer, String pos) {
    try { lexer.nextToken(); }
    catch (LexerException e) {
      assertTrue(e.getMessage().substring(0,pos.length()).equals(pos));
      return true;
    }
    return false;
  }

  @Test
  public void testIntegerZero() throws LexerException {
    Lexer lexer = createLexer("0");
    verifyToken(lexer.nextToken(), CoraTokenData.INTEGER, "0");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testPositiveInteger() throws LexerException {
    Lexer lexer = createLexer("30");
    verifyToken(lexer.nextToken(), CoraTokenData.INTEGER, "30");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLargePositiveInteger() throws LexerException {
    Lexer lexer = createLexer("1796974521107176491");
    verifyToken(lexer.nextToken(), CoraTokenData.INTEGER, "1796974521107176491");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testNegativeConstant() throws LexerException {
    Lexer lexer = createLexer("-x");
    verifyToken(lexer.nextToken(), CoraTokenData.MINUS, "-");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "x");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLargerNegativeInteger() throws LexerException {
    Lexer lexer = createLexer("-1208");
    verifyToken(lexer.nextToken(), CoraTokenData.MINUS, "-");
    verifyToken(lexer.nextToken(), CoraTokenData.INTEGER, "1208");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testDoubleZero() throws LexerException {
    Lexer lexer = createLexer("00");
    assertTrue(checkExceptionOnNextToken(lexer, "1:1:"));
    verifyToken(lexer.nextToken(), CoraTokenData.INTEGER, "0");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testStartWithZero() throws LexerException {
    Lexer lexer = createLexer(" 01234");
    assertTrue(checkExceptionOnNextToken(lexer, "1:2:"));
    verifyToken(lexer.nextToken(), CoraTokenData.INTEGER, "1234");
  }

  @Test
  public void testNegativeZero() throws LexerException {
    Lexer lexer = createLexer("\n-0");
    verifyToken(lexer.nextToken(), CoraTokenData.MINUS, "-");
    verifyToken(lexer.nextToken(), CoraTokenData.INTEGER, "0");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testMultipleNegatives() throws LexerException {
    Lexer lexer = createLexer("-132-7");
    verifyToken(lexer.nextToken(), CoraTokenData.MINUS, "-");
    verifyToken(lexer.nextToken(), CoraTokenData.INTEGER, "132");
    verifyToken(lexer.nextToken(), CoraTokenData.MINUS, "-");
    verifyToken(lexer.nextToken(), CoraTokenData.INTEGER, "7");
  }

  @Test
  public void testRecogniseTruth() throws LexerException {
    Lexer lexer = createLexer("true");
    verifyToken(lexer.nextToken(), CoraTokenData.TRUE, "true");
  }

  @Test
  public void testRecogniseFalsehood() throws LexerException {
    Lexer lexer = createLexer("false");
    verifyToken(lexer.nextToken(), CoraTokenData.FALSE, "false");
  }

  @Test
  public void testLexSimpleIdentifier() throws LexerException {
    Lexer lexer = createLexer("myfun");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "myfun");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testIdentifierStartingWithIntegers() throws LexerException {
    Lexer lexer = createLexer("1234abc");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "1234abc");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testIdentifierEndingWithIntegers() throws LexerException {
    Lexer lexer = createLexer("abc1234");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "abc1234");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexUnicodeIdentifier() throws LexerException {
    Lexer lexer = createLexer("émy∀fun");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "émy∀fun");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexWhitespaceBetweenIdentifiers() throws LexerException {
    Lexer lexer = createLexer("émy∀fun xx ∃ x ");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "émy∀fun");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "xx");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "∃");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "x");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testNumbersInIdentifier() throws LexerException {
    Lexer lexer = createLexer("a134710b");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "a134710b");
  }

  @Test
  public void testLexColons() throws LexerException {
    Lexer lexer;

    lexer = createLexer("::");
    verifyToken(lexer.nextToken(), CoraTokenData.DECLARE, "::");
    assertTrue(lexer.nextToken().isEof());

    lexer = createLexer(":");
    verifyToken(lexer.nextToken(), CoraTokenData.COLON, ":");
    assertTrue(lexer.nextToken().isEof());

    lexer = createLexer(":::");
    verifyToken(lexer.nextToken(), CoraTokenData.DECLARE, "::");
    verifyToken(lexer.nextToken(), CoraTokenData.COLON, ":");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexMid() throws LexerException {
    Lexer lexer;

    lexer = createLexer("|a");
    verifyToken(lexer.nextToken(), CoraTokenData.MID, "|");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "a");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testAllBasicTokens() throws LexerException {
    Lexer lexer = createLexer("xx⦈(y){,+#-\\a∀ \\/∃7*Q}():::a[b→b.]>c-+-3|7λ12≥a≤b" +
      "bae/\\a∧b<=c>=d∨e<f/g!=_Inttest");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "xx");
    verifyToken(lexer.nextToken(), CoraTokenData.TUPLECLOSE, "⦈");
    verifyToken(lexer.nextToken(), CoraTokenData.BRACKETOPEN, "(");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "y");
    verifyToken(lexer.nextToken(), CoraTokenData.BRACKETCLOSE, ")");
    verifyToken(lexer.nextToken(), CoraTokenData.BRACEOPEN, "{");
    verifyToken(lexer.nextToken(), CoraTokenData.COMMA, ",");
    verifyToken(lexer.nextToken(), CoraTokenData.PLUS, "+");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "#");
    verifyToken(lexer.nextToken(), CoraTokenData.MINUS, "-");
    verifyToken(lexer.nextToken(), CoraTokenData.LAMBDA, "\\");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "a∀");
    verifyToken(lexer.nextToken(), CoraTokenData.OR, "\\/");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "∃7");
    verifyToken(lexer.nextToken(), CoraTokenData.TIMES, "*");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "Q");
    verifyToken(lexer.nextToken(), CoraTokenData.BRACECLOSE, "}");
    verifyToken(lexer.nextToken(), CoraTokenData.BRACKETOPEN, "(");
    verifyToken(lexer.nextToken(), CoraTokenData.BRACKETCLOSE, ")");
    verifyToken(lexer.nextToken(), CoraTokenData.DECLARE, "::");
    verifyToken(lexer.nextToken(), CoraTokenData.COLON, ":");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "a");
    verifyToken(lexer.nextToken(), CoraTokenData.METAOPEN, "[");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "b");
    verifyToken(lexer.nextToken(), CoraTokenData.ARROW, "→");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "b");
    verifyToken(lexer.nextToken(), CoraTokenData.DOT, ".");
    verifyToken(lexer.nextToken(), CoraTokenData.METACLOSE, "]");
    verifyToken(lexer.nextToken(), CoraTokenData.GREATER, ">");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "c");
    verifyToken(lexer.nextToken(), CoraTokenData.MINUS, "-");
    verifyToken(lexer.nextToken(), CoraTokenData.PLUS, "+");
    verifyToken(lexer.nextToken(), CoraTokenData.MINUS, "-");
    verifyToken(lexer.nextToken(), CoraTokenData.INTEGER, "3");
    verifyToken(lexer.nextToken(), CoraTokenData.MID, "|");
    verifyToken(lexer.nextToken(), CoraTokenData.INTEGER, "7");
    verifyToken(lexer.nextToken(), CoraTokenData.LAMBDA, "λ");
    verifyToken(lexer.nextToken(), CoraTokenData.INTEGER, "12");
    verifyToken(lexer.nextToken(), CoraTokenData.GEQ, "≥");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "a");
    verifyToken(lexer.nextToken(), CoraTokenData.LEQ, "≤");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "bbae");
    verifyToken(lexer.nextToken(), CoraTokenData.AND, "/\\");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "a");
    verifyToken(lexer.nextToken(), CoraTokenData.AND, "∧");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "b");
    verifyToken(lexer.nextToken(), CoraTokenData.LEQ, "<=");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "c");
    verifyToken(lexer.nextToken(), CoraTokenData.GEQ, ">=");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "d");
    verifyToken(lexer.nextToken(), CoraTokenData.OR, "∨");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "e");
    verifyToken(lexer.nextToken(), CoraTokenData.SMALLER, "<");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "f");
    verifyToken(lexer.nextToken(), CoraTokenData.DIV, "/");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "g");
    verifyToken(lexer.nextToken(), CoraTokenData.UNEQUALINT, "!=_Int");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "test");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testArrowsInIdentifer() throws LexerException {
    Lexer lexer = createLexer("aa-b--->c⇒d<==><=>-->e");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "aa");
    verifyToken(lexer.nextToken(), CoraTokenData.MINUS, "-");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "b");
    verifyToken(lexer.nextToken(), CoraTokenData.MINUS, "-");
    verifyToken(lexer.nextToken(), CoraTokenData.MINUS, "-");
    verifyToken(lexer.nextToken(), CoraTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "c⇒d");
    verifyToken(lexer.nextToken(), CoraTokenData.LEQ, "<=");
    verifyToken(lexer.nextToken(), CoraTokenData.EQUAL, "=");
    verifyToken(lexer.nextToken(), CoraTokenData.GREATER, ">");
    verifyToken(lexer.nextToken(), CoraTokenData.EQUALBOOL, "<=>");
    verifyToken(lexer.nextToken(), CoraTokenData.MINUS, "-");
    verifyToken(lexer.nextToken(), CoraTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "e");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testPartialArrows() throws LexerException {
    Lexer lexer = createLexer("-> - > x->y");
    verifyToken(lexer.nextToken(), CoraTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), CoraTokenData.MINUS, "-");
    verifyToken(lexer.nextToken(), CoraTokenData.GREATER, ">");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "x");
    verifyToken(lexer.nextToken(), CoraTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "y");
  }

  @Test
  public void testRemoveSimpleComment() throws LexerException {
    Lexer lexer = createLexer("xx /*test*/ yy");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "xx");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "yy");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testRemoveCommentWithoutSpacing() throws LexerException {
    Lexer lexer = createLexer("xx/*test*/yy");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "xx");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "yy");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testRemoveNestedComment() throws LexerException {
    Lexer lexer = createLexer("xx /* ab /* cd */ ef */ yy");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "xx");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "yy");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testRemoveNestedCommentButAllowMultiplication() throws LexerException {
    Lexer lexer = createLexer("x*x*a/***u/***3*/***/*yy");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "x");
    verifyToken(lexer.nextToken(), CoraTokenData.TIMES, "*");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "x");
    verifyToken(lexer.nextToken(), CoraTokenData.TIMES, "*");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "a");
    verifyToken(lexer.nextToken(), CoraTokenData.TIMES, "*");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "yy");
  }

  @Test
  public void testSlashAndStarSplitInIdentifier() throws LexerException {
    Lexer lexer = createLexer("a/b*c");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "a");
    verifyToken(lexer.nextToken(), CoraTokenData.DIV, "/");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "b");
    verifyToken(lexer.nextToken(), CoraTokenData.TIMES, "*");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "c");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testStrayCommentClosing() throws LexerException {
    Lexer lexer = createLexer("asd a */}");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "asd");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "a");
    assertTrue(checkExceptionOnNextToken(lexer, "1:7:"));
    verifyToken(lexer.nextToken(), CoraTokenData.BRACECLOSE, "}");
  }

  @Test
  public void testStrayCommentClosingInIdentifier() throws LexerException {
    Lexer lexer = createLexer("asd a*/");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "asd");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "a");
    assertTrue(checkExceptionOnNextToken(lexer, "1:6:"));
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testStrayCommentClosingInIdentifierWithStarsAtTheEnd() throws LexerException {
    Lexer lexer = createLexer("asd**/*");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "asd");
    verifyToken(lexer.nextToken(), CoraTokenData.TIMES, "*");
    assertTrue(checkExceptionOnNextToken(lexer, "1:5:"));
    verifyToken(lexer.nextToken(), CoraTokenData.TIMES, "*");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testStrayCommentCloseAfterComment() throws LexerException {
    Lexer lexer = createLexer("/* bing */ */");
    assertTrue(checkExceptionOnNextToken(lexer, "1:12:"));
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testUnterminatedComment() throws LexerException {
    Lexer lexer = createLexer("bing /* bong");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "bing");
    assertTrue(checkExceptionOnNextToken(lexer, "1:6:"));
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testUnterminatedCommentAtIdentifierEnd() throws LexerException {
    Lexer lexer = createLexer("bing/*bong");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "bing");
    assertTrue(checkExceptionOnNextToken(lexer, "1:5:"));
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testBasicString() throws LexerException {
    Lexer lexer = createLexer("x\"xz\"uv");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "x");
    verifyToken(lexer.nextToken(), CoraTokenData.STRING, "\"xz\"");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "uv");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testStringWithStuffInIt() throws LexerException {
    Lexer lexer = createLexer("x\"x/*z{\"uv");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "x");
    verifyToken(lexer.nextToken(), CoraTokenData.STRING, "\"x/*z{\"");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "uv");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testStringWithEscapeCodes() throws LexerException {
    Lexer lexer = createLexer("\"x\\\"bl\\\\a\"bla");
    verifyToken(lexer.nextToken(), CoraTokenData.STRING, "\"x\\\"bl\\\\a\"");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "bla");
  }

  @Test
  public void testUnterminatedStringEOF() throws LexerException {
    Lexer lexer = createLexer("\n\"bla");
    assertTrue(checkExceptionOnNextToken(lexer, "2:1:"));
    verifyToken(lexer.nextToken(), CoraTokenData.STRING, "\"bla\"");
  }

  @Test
  public void testUnterminatedStringEndLine() throws LexerException {
    Lexer lexer = createLexer("\"bla\n20 bla\"");
    assertTrue(checkExceptionOnNextToken(lexer, "1:1:"));
    verifyToken(lexer.nextToken(), CoraTokenData.STRING, "\"bla\n\"");
    verifyToken(lexer.nextToken(), CoraTokenData.INTEGER, "20");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "bla");
    assertTrue(checkExceptionOnNextToken(lexer, "2:7:"));
    verifyToken(lexer.nextToken(), CoraTokenData.STRING, "\"\"");
  }

  @Test
  public void testIllegalEscape() throws LexerException {
    Lexer lexer = createLexer("\"hello\\x World\"");
    verifyToken(lexer.nextToken(), CoraTokenData.STRING, "\"hello\\x World\"");
  }

  @Test
  public void testStringEndsInEscape() throws LexerException {
    Lexer lexer = createLexer("\n\"bla\\");
    assertTrue(checkExceptionOnNextToken(lexer, "2:1:"));
    verifyToken(lexer.nextToken(), CoraTokenData.STRING, "\"bla\\\"");
  }
}

