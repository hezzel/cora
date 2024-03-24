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

package charlie.parser.lib;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class CommentRemoverLexerTest {
  private Lexer makeLexer(String str, boolean nested) {
    Lexer baselexer = LexerFactory.createStringLexer(new String[] {
                                       "\\w*", "IDENTIFIER",
                                       "\\s+", Token.SKIP,
                                       "\\([*]", "COMMENTOPEN",
                                       "[*]\\)", "COMMENTCLOSE"
                                    }, str);
    if (nested) {
      return LexerFactory.createNestedCommentRemoverLexer(baselexer, "COMMENTOPEN", "COMMENTCLOSE");
    }
    else {
      return LexerFactory.createBasicCommentRemoverLexer(baselexer, "COMMENTOPEN", "COMMENTCLOSE");
    }
  }

  @Test
  public void testNonNestedRemoval() throws LexerException {
    Lexer lexer = makeLexer("hello (* this \n is a comment (* is it not? *) world *)aa", false);
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("1:1: hello (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:32: world (IDENTIFIER)"));
    boolean errored = false;
    try { lexer.nextToken(); }
    catch (LexerException e) {
      errored = true;
      assertTrue(e.getMessage().equals(
        "2:38: unexpected comment-close token [*)] when no comment was open!"));
    }
    assertTrue(errored);
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:40: aa (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
  }

  @Test
  public void testNestedRemoval() throws LexerException {
    Lexer lexer = makeLexer("hello (* this \n is a comment (* is it not? *) worl\nd *)aa", true);
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("1:1: hello (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("3:5: aa (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
  }

  @Test
  public void testCannotUseEofAsComentOpen() throws LexerException {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "\\w*", "IDENTIFIER",
                                       "\\s+", "SKIP",
                                       "\\([*]", "COMMENTOPEN",
                                       "[*]\\)", "COMMENTCLOSE"
                                     });
    Lexer baselexer = new MultilineStringLexer(tf, "hello");
    Lexer lexer = new CommentRemoverLexer(baselexer, "EOF", "COMMENTCLOSE", true);
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("1:1: hello (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
  }

  @Test
  public void testCannotUseEofAsComentClose() throws LexerException {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "\\w*", "IDENTIFIER",
                                       "\\s+", "WHITESPACE",
                                       "\\([*]", "COMMENTOPEN",
                                       "[*]\\)", "COMMENTCLOSE"
                                     });
    Lexer baselexer = new MultilineStringLexer(tf, "hello (* bing");
    Lexer lexer = new CommentRemoverLexer(baselexer, "COMMENTOPEN", "EOF", true);
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("1:1: hello (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:6:   (WHITESPACE)"));
    assertThrows(LexerException.class, () -> lexer.nextToken());
  }

  @Test
  public void testUnclosedBlock() throws LexerException {
    Lexer lexer = makeLexer("hello (* this \n is a comment \n", false);
    Token token = lexer.nextToken();    // IDENTIFIER
    try { token = lexer.nextToken(); }
    catch (LexerException e) {
      assertTrue(e.getMessage().equals(
        "1:7: end of input was reached before comment [(*] was closed"));
      return;
    }
    assertTrue(false);  // we should have returned in the catch!
  }

  @Test
  public void testUnclosedNestedBlock() throws LexerException {
    Lexer lexer = makeLexer("hello (* this \n is (* a comment \n", false);
    Token token = lexer.nextToken();    // IDENTIFIER
    try { token = lexer.nextToken(); }
    catch (LexerException e) {
      assertTrue(e.getMessage().equals(
        "1:7: end of input was reached before comment [(*] was closed"));
      return;
    }
    assertTrue(false);  // we should have returned in the catch!
  }
}

