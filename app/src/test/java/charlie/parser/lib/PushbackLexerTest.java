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

public class PushbackLexerTest {
  @Test
  public void testPushAndPull() throws LexerException {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "[a-zA-Z_][a-z0-9A-Z_]*", "IDENTIFIER",
                                       "0|[1-9][0-9]*", "INTEGER",
                                       "\\s", "SKIP" });
    Lexer sublexer = new StringLexer(tf, "hello world \n1234 toot\n");
    TokenQueue lexer = new PushbackLexer(sublexer);
    Token first = lexer.nextToken();
    assertTrue(first.toString().equals("1: hello (IDENTIFIER)"));
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("7: world (IDENTIFIER)"));
    lexer.push(token);
    lexer.push(token);
    lexer.push(new Token(new ParsePosition("xx", 19, 4), "BLAAT", "text"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("xx:19:4: text (BLAAT)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("7: world (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("7: world (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("14: 1234 (INTEGER)"));
    lexer.push(first);
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1: hello (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("19: toot (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
    token = lexer.nextToken();
    assertTrue(token.isEof());
  }
}

