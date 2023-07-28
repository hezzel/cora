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
import java.util.TreeSet;
import cora.parsing.lib.Token;
import cora.parsing.lib.LexerException;
import cora.parsing.lib.Lexer;

public class CoraTokensTest {
  private TreeSet<String> errors;

  private Lexer createLexer(String str) {
    errors = new TreeSet<String>();
    return CoraTokenData.getStringLexer(str);
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
  public void testLexSimpleIdentifier() throws LexerException {
    Lexer lexer = createLexer("myfun");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "myfun");
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
  public void testAllBasicTokens() throws LexerException {
    Lexer lexer = createLexer("xx(y){,+#\\a∀ ∃7*}():::a[b→b.⇒]>c--λ12");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "xx");
    verifyToken(lexer.nextToken(), CoraTokenData.BRACKETOPEN, "(");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "y");
    verifyToken(lexer.nextToken(), CoraTokenData.BRACKETCLOSE, ")");
    verifyToken(lexer.nextToken(), CoraTokenData.BRACEOPEN, "{");
    verifyToken(lexer.nextToken(), CoraTokenData.COMMA, ",");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "+#");
    verifyToken(lexer.nextToken(), CoraTokenData.LAMBDA, "\\");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "a∀");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "∃7*");
    verifyToken(lexer.nextToken(), CoraTokenData.BRACECLOSE, "}");
    verifyToken(lexer.nextToken(), CoraTokenData.BRACKETOPEN, "(");
    verifyToken(lexer.nextToken(), CoraTokenData.BRACKETCLOSE, ")");
    verifyToken(lexer.nextToken(), CoraTokenData.DECLARE, "::");
    verifyToken(lexer.nextToken(), CoraTokenData.COLON, ":");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "a");
    verifyToken(lexer.nextToken(), CoraTokenData.METAOPEN, "[");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "b");
    verifyToken(lexer.nextToken(), CoraTokenData.RULEARROW, "→");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "b");
    verifyToken(lexer.nextToken(), CoraTokenData.DOT, ".");
    verifyToken(lexer.nextToken(), CoraTokenData.TYPEARROW, "⇒");
    verifyToken(lexer.nextToken(), CoraTokenData.METACLOSE, "]");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, ">c--");
    verifyToken(lexer.nextToken(), CoraTokenData.LAMBDA, "λ");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "12");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testArrowsInIdentifer() throws LexerException {
    Lexer lexer = createLexer("aa-b--->c⇒d=>-->e");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "aa-b--");
    verifyToken(lexer.nextToken(), CoraTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "c");
    verifyToken(lexer.nextToken(), CoraTokenData.TYPEARROW, "⇒");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "d=>-");
    verifyToken(lexer.nextToken(), CoraTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "e");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testPartialArrows() throws LexerException {
    Lexer lexer = createLexer("-> - > x->y");
    verifyToken(lexer.nextToken(), CoraTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "-");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, ">");
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
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "x*x*a");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "*yy");
  }

  @Test
  public void testSlashAllowedAsIdentifier() throws LexerException {
    Lexer lexer = createLexer("/");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "/");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testStarAllowedAsIdentifier() throws LexerException {
    Lexer lexer = createLexer("*");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "*");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testSlashAndStarAllowedInIdentifier() throws LexerException {
    Lexer lexer = createLexer("a/b*c");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "a/b*c");
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
    Lexer lexer = createLexer("asd****/*");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "asd***");
    assertTrue(checkExceptionOnNextToken(lexer, "1:7:"));
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "*");
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
    Lexer lexer = createLexer("\"bla\nmeer bla\"");
    assertTrue(checkExceptionOnNextToken(lexer, "1:1:"));
    verifyToken(lexer.nextToken(), CoraTokenData.STRING, "\"bla\"");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "meer");
    verifyToken(lexer.nextToken(), CoraTokenData.IDENTIFIER, "bla");
    assertTrue(checkExceptionOnNextToken(lexer, "2:9:"));
    verifyToken(lexer.nextToken(), CoraTokenData.STRING, "\"\"");
  }

  @Test
  public void testIllegalEscape() throws LexerException {
    Lexer lexer = createLexer("\"hello\\x World\"");
    assertTrue(checkExceptionOnNextToken(lexer, "1:1:"));
    verifyToken(lexer.nextToken(), CoraTokenData.STRING, "\"hello\\x World\"");
  }

  @Test
  public void testStringEndsInEscape() throws LexerException {
    Lexer lexer = createLexer("\n\"bla\\");
    assertTrue(checkExceptionOnNextToken(lexer, "2:1:"));
    verifyToken(lexer.nextToken(), CoraTokenData.STRING, "\"bla\\\"");
  }
}

