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

public class MultilineStringLexerTest {
  @Test
  public void testLexer() throws LexerException {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "[a-zA-Z_][a-z0-9A-Z_]*", "IDENTIFIER",
                                       "0|[1-9][0-9]*", "INTEGER",
                                       "\\s+", "WHITESPACE" });
    Lexer lexer = new MultilineStringLexer(tf, "BING \n  12\r\n31 *_a10?\n0");
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("1:1: BING (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:5:  \n (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:1:    (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:3: 12 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:5: \n (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("3:1: 31 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("3:3:   (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("3:4: * (CATCHALL)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("3:5: _a10 (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("3:9: ? (CATCHALL)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("3:10: \n (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("4:1: 0 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
    assertTrue(token.toString().equals("4:2:  (EOF)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
    assertTrue(token.toString().equals("5:1:  (EOF)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("5:1:  (EOF)"));
  }

  @Test
  public void testSwitchMode() throws LexerException {
    TokenFinder tf1 = new TokenFinder(new String[] {
                                        "[a-zA-Z_][a-z0-9A-Z_]*", "IDENTIFIER",
                                        "0|[1-9][0-9]*", "INTEGER",
                                        "\\s+", "WHITESPACE" });
    TokenFinder tf2 = new TokenFinder(new String[] {
                                        "[^a]+", "NOTA",
                                        "a", "A",
                                      });
    ModeLexer lexer = new MultilineStringLexer(tf1, "hello sweet world!\n How are you todaaaay?");
    assertTrue(lexer.nextToken().toString().equals("1:1: hello (IDENTIFIER)"));
    lexer.switchMode(tf2);
    assertTrue(lexer.nextToken().toString().equals("1:6:  sweet world!\n (NOTA)"));
    assertTrue(lexer.nextToken().toString().equals("2:1:  How  (NOTA)"));
    assertTrue(lexer.nextToken().toString().equals("2:6: a (A)"));
    lexer.switchMode(tf1);
    assertTrue(lexer.nextToken().toString().equals("2:7: re (IDENTIFIER)"));
  }
}

