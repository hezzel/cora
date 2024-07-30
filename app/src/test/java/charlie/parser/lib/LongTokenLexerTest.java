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

public class LongTokenLexerTest {
  @Test
  public void testBasics() throws LexerException {
    ChangeableLexer lexer = LexerFactory.createStringLexer(new String[] {
                                     "\\w*", "IDENTIFIER",
                                     "\\s+", Token.SKIP,
                                     "\\|", "STRINGSTART",
                                   }, "Hello world! |bing bang| toot |test\n bla  | dododo");
    lexer = LexerFactory.createLongTokenLexer(lexer, "STRINGSTART", "[^|]+", "\\|", "STRING");
    Token token;
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:1: Hello (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:7: world (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:12: ! (CATCHALL)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:14: |bing bang| (STRING)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:26: toot (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:31: |test\n bla  | (STRING)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:9: dododo (IDENTIFIER)"));
  }

  @Test
  public void testSkip() throws LexerException {
    ChangeableLexer lexer = LexerFactory.createStringLexer(new String[] {
                                     "\\w*", "IDENTIFIER",
                                     "\\s+", Token.SKIP,
                                     "\\|", "STRINGSTART",
                                   }, "Hello world! |bing bang| toot |test\n bla  | dododo");
    lexer = LexerFactory.createLongTokenLexer(lexer, "STRINGSTART", "[^|]+", "\\|", Token.SKIP);
    assertTrue(lexer.nextToken().toString().equals("1:1: Hello (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals("1:7: world (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals("1:12: ! (CATCHALL)"));
    assertTrue(lexer.nextToken().toString().equals("1:26: toot (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals("2:9: dododo (IDENTIFIER)"));
  }

  @Test
  public void testBadLongToken() throws LexerException {
    ChangeableLexer lexer = LexerFactory.createStringLexer(new String[] {
                                     "\\w*", "IDENTIFIER",
                                     "\\s+", Token.SKIP,
                                     "\\|", "STRINGSTART",
                                   }, "Hello world! |bingbang| toot |test\n bla  |dododo");
    lexer = LexerFactory.createLongTokenLexer(lexer, "STRINGSTART", "[a-z]+", "\\|", "STRING");
    Token token;
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:1: Hello (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:7: world (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:12: ! (CATCHALL)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:14: |bingbang| (STRING)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:25: toot (IDENTIFIER)"));
    Lexer tmp1 = lexer;
    assertThrows(LexerException.class, () -> tmp1.nextToken());
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:2: bla (IDENTIFIER)"));
    Lexer tmp2 = lexer;
    assertThrows(LexerException.class, () -> tmp2.nextToken());
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testCombineLexer() throws LexerException {
    ChangeableLexer lexer = LexerFactory.createStringLexer(new String[] {
                                     "\\w*", "IDENTIFIER",
                                     "\\s+", Token.SKIP,
                                     "\\|", "SPECIALSTART",
                                     "\\\"", "STRINGSTART",
                                   }, "abc def \"ge | \\\"de\" hello|thin\ngy| |random\"quote\"|.");
    lexer = LexerFactory.createLongTokenLexer(lexer, "SPECIALSTART", "[^|]+", "\\|", "P");
    lexer = LexerFactory.createLongTokenLexer(lexer, "STRINGSTART", "([^\\\\]|\\\\\")", "\\\"", "I");
    assertTrue(lexer.nextToken().toString().equals("1:1: abc (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals("1:5: def (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals("1:9: \"ge | \\\"de\" (I)"));
    assertTrue(lexer.nextToken().toString().equals("1:21: hello (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals("1:26: |thin\ngy| (P)"));
    assertTrue(lexer.nextToken().toString().equals("2:5: |random\"quote\"| (P)"));
    assertTrue(lexer.nextToken().toString().equals("2:20: . (CATCHALL)"));
  }

/*
  @Test
  public void testLongTokenLexerFromFile() throws LexerException, java.io.IOException {
    String fname = "test.txt";
    ChangeableLexer lexer = LexerFactory.createFileLexer(new String[] {
                                     "\\w*", "IDENTIFIER",
                                     "\\s+", Token.SKIP,
                                     "\\|", "STRINGSTART",
                                   }, fname);
    lexer = LexerFactory.createLongTokenLexer(lexer, "STRINGSTART", "[^|]+", "\\|", "STRING");
    assertTrue(lexer.nextToken().toString().equals(fname + ":1:1: abc (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals(fname + ":1:5: |def| (STRING)"));
    assertTrue(lexer.nextToken().toString().equals(fname + ":1:11: gij (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals(fname + ":1:15: |klm\nnop| (STRING)"));
    assertTrue(lexer.nextToken().toString().equals(fname + ":2:5: qrs (IDENTIFIER)"));
  }
*/
}

