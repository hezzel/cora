/**************************************************************************************************
 Copyright 2019, 2022 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.lib.parsers;

import org.junit.Test;
import static org.junit.Assert.*;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Token;
import java.util.ArrayList;

public class CoraLexerTest {
  private ArrayList<String> warnings;

  private CoraLexer createLexer(String str) {
    return new CoraLexer(CharStreams.fromString(str));
  }

  private ArrayList<Token> tokenise(String str) {
    CoraLexer lexer = createLexer(str);
    ArrayList<Token> ret = new ArrayList<Token>();
    while (true) {
      Token tk = lexer.nextToken();
      if (tk.getType() == Token.EOF) break;
      ret.add(tk);
    }
    warnings = lexer.queryWarnings();
    return ret;
  }

  private void verifyToken(Token tk, int kind, String text) {
    assertTrue(tk.getType() == kind);
    assertTrue(tk.getText().equals(text));
  }

  private void verifyError(int i, int line, int pos) {
    assertTrue(warnings.size() > i);
    String posdesc = "" + line + ":" + pos + ": ";
    assertTrue(warnings.get(i).substring(0, posdesc.length()).equals(posdesc));
  }

  private void verifyError(int line, int pos) {
    verifyError(0, line, pos);
  }

  @Test
  public void testLexSimpleIdentifier() {
    ArrayList<Token> parts = tokenise("myfun");
    assertTrue(parts.size() == 1);
    assertTrue(parts.get(0).getType() == CoraLexer.IDENTIFIER);
    assertTrue(parts.get(0).getText().equals("myfun"));
  }

  @Test
  public void testLexUnicodeIdentifier() {
    ArrayList<Token> parts = tokenise("émy∀fun");
    assertTrue(parts.size() == 1);
    verifyToken(parts.get(0), CoraLexer.IDENTIFIER, "émy∀fun");
  }

  @Test
  public void testLexWhitespaceBetweenIdentifiers() {
    ArrayList<Token> parts = tokenise("émy∀fun xx ∃ x ");
    assertTrue(parts.size() == 4);
    verifyToken(parts.get(0), CoraLexer.IDENTIFIER, "émy∀fun");
    verifyToken(parts.get(3), CoraLexer.IDENTIFIER, "x");
  }

  @Test
  public void testLexColons() {
    ArrayList<Token> parts = tokenise("::");
    assertTrue(parts.size() == 1);
    assertTrue(parts.get(0).getType() == CoraLexer.DECLARE);

    parts = tokenise(":");
    assertTrue(parts.size() == 1);
    assertTrue(parts.get(0).getType() == CoraLexer.COLON);

    parts = tokenise(":::");
    assertTrue(parts.size() == 2);
    assertTrue(parts.get(0).getType() == CoraLexer.DECLARE);
    assertTrue(parts.get(1).getType() == CoraLexer.COLON);
  }

  @Test
  public void testAllBasicTokens() {
    ArrayList<Token> parts = tokenise("xx(y){,+#\\a∀ ∃7*}():::a[b→b.]cλ");
    assertTrue(parts.size() == 22);
    assertTrue(parts.get(0).getType() == CoraLexer.IDENTIFIER);
    assertTrue(parts.get(1).getType() == CoraLexer.BRACKETOPEN);
    assertTrue(parts.get(2).getType() == CoraLexer.IDENTIFIER);
    assertTrue(parts.get(3).getType() == CoraLexer.BRACKETCLOSE);
    assertTrue(parts.get(4).getType() == CoraLexer.BRACEOPEN);
    assertTrue(parts.get(5).getType() == CoraLexer.COMMA);
    assertTrue(parts.get(6).getType() == CoraLexer.IDENTIFIER);
    assertTrue(parts.get(7).getType() == CoraLexer.LAMBDA);
    assertTrue(parts.get(8).getType() == CoraLexer.IDENTIFIER);
    assertTrue(parts.get(9).getType() == CoraLexer.IDENTIFIER);
    assertTrue(parts.get(10).getType() == CoraLexer.BRACECLOSE);
    assertTrue(parts.get(11).getType() == CoraLexer.BRACKETOPEN);
    assertTrue(parts.get(12).getType() == CoraLexer.BRACKETCLOSE);
    assertTrue(parts.get(13).getType() == CoraLexer.DECLARE);
    assertTrue(parts.get(14).getType() == CoraLexer.COLON);
    assertTrue(parts.get(16).getType() == CoraLexer.SQUAREOPEN);
    assertTrue(parts.get(18).getType() == CoraLexer.DOT);
    assertTrue(parts.get(19).getType() == CoraLexer.SQUARECLOSE);
    assertTrue(parts.get(21).getType() == CoraLexer.LAMBDA);
  }

  @Test
  public void testRemoveSimpleComment() {
    ArrayList<Token> parts = tokenise("xx /*test*/ yy");
    assertTrue(parts.size() == 2);
    assertTrue(parts.get(0).getText().equals("xx"));
    assertTrue(parts.get(1).getText().equals("yy"));
  }

  @Test
  public void testRemoveCommentWithoutSpacing() {
    ArrayList<Token> parts = tokenise("xx/*test*/yy");
    assertTrue(parts.size() == 2);
    assertTrue(parts.get(0).getText().equals("xx"));
    assertTrue(parts.get(1).getText().equals("yy"));
  }

  @Test
  public void testRemoveNestedComment() {
    ArrayList<Token> parts = tokenise("xx /* ab /* cd */ ef */ yy");
    assertTrue(parts.size() == 2);
    assertTrue(parts.get(0).getText().equals("xx"));
    assertTrue(parts.get(1).getText().equals("yy"));
  }

  @Test
  public void testRemoveNestedCommentButAllowMultiplication() {
    ArrayList<Token> parts = tokenise("x*x*a/***u/***3*/***/*yy");
    assertTrue(parts.size() == 2);
    verifyToken(parts.get(0), CoraLexer.IDENTIFIER, "x*x*a");
    verifyToken(parts.get(1), CoraLexer.IDENTIFIER, "*yy");
  }

  @Test
  public void testSlashAllowedAsIdentifier() {
    ArrayList<Token> parts = tokenise("/");
    assertTrue(parts.size() == 1);
    verifyToken(parts.get(0), CoraLexer.IDENTIFIER, "/");
  }

  @Test
  public void testStarAllowedAsIdentifier() {
    ArrayList<Token> parts = tokenise("*");
    assertTrue(parts.size() == 1);
    verifyToken(parts.get(0), CoraLexer.IDENTIFIER, "*");
  }

  @Test
  public void testSlashAndStarAllowedInIdentifier() {
    ArrayList<Token> parts = tokenise("a/b*c");
    assertTrue(parts.size() == 1);
    verifyToken(parts.get(0), CoraLexer.IDENTIFIER, "a/b*c");
  }

  @Test
  public void testStrayCommentClosing() {
    ArrayList<Token> parts = tokenise("asd a */}");
    assertTrue(parts.size() == 3);
    verifyError(1, 7);
    verifyToken(parts.get(2), CoraLexer.BRACECLOSE, "}");
  }

  @Test
  public void testStrayCommentClosingInIdentifier() {
    ArrayList<Token> parts = tokenise("asd a*/");
    assertTrue(parts.size() == 2);
    verifyError(1, 6);
  }

  @Test
  public void testStrayCommentClosingInIdentifierWithStarsAtTheEnd() {
    ArrayList<Token> parts = tokenise("asd****/*");
    assertTrue(parts.size() == 2);
    verifyToken(parts.get(0), CoraLexer.IDENTIFIER, "asd***");
    verifyToken(parts.get(1), CoraLexer.IDENTIFIER, "*");
    verifyError(1, 7);
  }

  @Test
  public void testStrayCommentCloseAfterComment() {
    ArrayList<Token> parts = tokenise("/* bing */ */");
    assertTrue(parts.size() == 0);
    verifyError(1, 12);
  }

  @Test
  public void testUnterminatedComment() {
    ArrayList<Token> parts = tokenise("bing /* bong");
    assertTrue(parts.size() == 1);
    verifyError(1, 6);
  }

  @Test
  public void testUnterminatedCommentAtIdentifierEnd() {
    ArrayList<Token> parts = tokenise("bing/*bong*");
    assertTrue(parts.size() == 1);
    verifyToken(parts.get(0), CoraLexer.IDENTIFIER, "bing");
    verifyError(1, 5);
  }

  @Test
  public void testBasicString() {
    ArrayList<Token> parts = tokenise("x\"xz\"uv");
    assertTrue(parts.size() == 3);
    verifyToken(parts.get(0), CoraLexer.IDENTIFIER, "x");
    verifyToken(parts.get(1), CoraLexer.STRING, "xz");
    verifyToken(parts.get(2), CoraLexer.IDENTIFIER, "uv");
  }

  @Test
  public void testStringWithStuffInit() {
    ArrayList<Token> parts = tokenise("x\"x/*z{\"uv");
    assertTrue(parts.size() == 3);
    verifyToken(parts.get(0), CoraLexer.IDENTIFIER, "x");
    verifyToken(parts.get(1), CoraLexer.STRING, "x/*z{");
    verifyToken(parts.get(2), CoraLexer.IDENTIFIER, "uv");
  }

  @Test
  public void testStringWithEscapeCodes() {
    ArrayList<Token> parts = tokenise("\"x\\\"bl\\\\a\"bla");
    assertTrue(parts.size() == 2);
    verifyToken(parts.get(0), CoraLexer.STRING, "x\"bl\\a");
  }

  @Test
  public void testUnterminatedStringEOF() {
    ArrayList<Token> parts = tokenise("\n\"bla");
    assertTrue(parts.size() == 1);
    verifyToken(parts.get(0), CoraLexer.STRING, "bla");
    verifyError(2, 1);
  }

  @Test
  public void testUnterminatedStringEndLine() {
    ArrayList<Token> parts = tokenise("\"bla\n\"");
    assertTrue(parts.size() == 2);
    verifyToken(parts.get(0), CoraLexer.STRING, "bla");
    verifyToken(parts.get(1), CoraLexer.STRING, "");
    verifyError(0, 1, 1);
    verifyError(1, 2, 1);
  }

  @Test
  public void testMultilineString() {
    ArrayList<Token> parts = tokenise("Hello\"bla\\\n\rWorld\"\"bing\"");
    assertTrue(parts.size() == 3);
    verifyToken(parts.get(1), CoraLexer.STRING, "bla\nWorld");
    verifyToken(parts.get(2), CoraLexer.STRING, "bing");
  }

  @Test
  public void testIllegalEscape() {
    ArrayList<Token> parts = tokenise("\"hello\\x World\"");
    assertTrue(parts.size() == 1);
    verifyToken(parts.get(0), CoraLexer.STRING, "hellox World");
    verifyError(1, 7);
  }

  @Test
  public void testStringEndsInEscape() {
    ArrayList<Token> parts = tokenise("\n\"bla\\");
    assertTrue(parts.size() == 1);
    verifyError(2, 1);
  }

  @Test
  public void testArrow() {
    ArrayList<Token> parts = tokenise("-> - > x->y");
    assertTrue(parts.size() == 4);
    assertTrue(parts.get(0).getType() == CoraLexer.ARROW);
    assertTrue(parts.get(1).getType() == CoraLexer.IDENTIFIER);
    assertTrue(parts.get(2).getType() == CoraLexer.IDENTIFIER);
    assertTrue(parts.get(3).getType() == CoraLexer.IDENTIFIER);
  }

  @Test
  public void testKeywordInclude() {
    ArrayList<Token> parts = tokenise("include");
    assertTrue(parts.get(0).getType() == CoraLexer.INCLUDE);
  }

  @Test
  public void testKeywordSort() {
    ArrayList<Token> parts = tokenise(" SoRt)");
    assertTrue(parts.get(0).getType() == CoraLexer.SORT);
  }

  @Test
  public void testKeywordOperator() {
    ArrayList<Token> parts = tokenise("}OPERATOR");
    assertTrue(parts.get(1).getType() == CoraLexer.OPERATOR);
  }

  @Test
  public void testKeywordTheory() {
    ArrayList<Token> parts = tokenise("theorY");
    assertTrue(parts.get(0).getType() == CoraLexer.THEORY);
  }

  @Test
  public void testKeywordAliasTranslate() {
    ArrayList<Token> parts = tokenise("ALIAS translate");
    assertTrue(parts.get(0).getType() == CoraLexer.ALIAS);
    assertTrue(parts.get(1).getType() == CoraLexer.TRANSLATE);
  }

  @Test
  public void testKeywordDisplay() {
    ArrayList<Token> parts = tokenise("display ");
    assertTrue(parts.get(0).getType() == CoraLexer.DISPLAY);
  }

  @Test
  public void testKeywordChain() {
    ArrayList<Token> parts = tokenise("CHAIN");
    assertTrue(parts.get(0).getType() == CoraLexer.CHAIN);
  }
}

