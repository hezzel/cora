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

public class StringLexerTest {
  @Test
  public void testBasicLexer() throws LexerException {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "[a-zA-Z_][a-z0-9A-Z_]*", "IDENTIFIER",
                                       "0|[1-9][0-9]*", "INTEGER",
                                       "\\s", "WHITESPACE" });
    Lexer lexer = new StringLexer(tf, "BING  1231 *_a10?\n00	x");
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("1: BING (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("5:   (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("6:   (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("7: 1231 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("11:   (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("12: * (CATCHALL)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("13: _a10 (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("17: ? (CATCHALL)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("18: \n (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("19: 0 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("20: 0 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("21: 	 (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("22: x (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
    token = lexer.nextToken();
    assertTrue(token.isEof());
  }

  @Test
  public void testLexerWithSkip() {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "[a-zA-Z_][a-z0-9A-Z_]*", "IDENTIFIER",
                                       "0|[1-9][0-9]*", "INTEGER",
                                       "\\s", Token.SKIP });
    StringLexer lexer = new StringLexer(tf, "BING  1231 *_a10?\n00	x");
    lexer.setFilename("aa");
    lexer.setLineNumber(9);
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("aa:9:1: BING (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("aa:9:7: 1231 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("aa:9:12: * (CATCHALL)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("aa:9:13: _a10 (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("aa:9:17: ? (CATCHALL)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("aa:9:19: 0 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("aa:9:20: 0 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("aa:9:22: x (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
    token = lexer.nextToken();
    assertTrue(token.isEof());
  }

  @Test
  public void testSwitchTokeniser() {
    TokenFinder tf1 = new TokenFinder(new String[] {
                                        "[a-zA-Z_][a-z0-9A-Z_]*", "IDENTIFIER",
                                        "0|[1-9][0-9]*", "INTEGER",
                                        "\\s", Token.SKIP });
    TokenFinder tf2 = new TokenFinder(new String[] {
                                        "[0-9]", "DIGIT",
                                        ".", "CHARACTER",
                                      });
    StringLexer lexer = new StringLexer(tf1, "ABC d1 341");
    lexer.setFilename("fname");
    lexer.setLineNumber(4);
    assertTrue(lexer.nextToken().toString().equals("fname:4:1: ABC (IDENTIFIER)"));
    lexer.changeTokenData(tf2);
    assertTrue(lexer.nextToken().toString().equals("fname:4:4:   (CHARACTER)"));
    assertTrue(lexer.nextToken().toString().equals("fname:4:5: d (CHARACTER)"));
    assertTrue(lexer.nextToken().toString().equals("fname:4:6: 1 (DIGIT)"));
    assertTrue(lexer.nextToken().toString().equals("fname:4:7:   (CHARACTER)"));
    assertTrue(lexer.nextToken().toString().equals("fname:4:8: 3 (DIGIT)"));
    lexer.changeTokenData(tf1);
    assertTrue(lexer.nextToken().toString().equals("fname:4:9: 41 (INTEGER)"));
  }
}

