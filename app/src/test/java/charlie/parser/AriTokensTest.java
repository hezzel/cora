/**************************************************************************************************
 Copyright 2024 Cynthia Kop

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

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.parser.lib.Token;
import charlie.parser.lib.LexerException;
import charlie.parser.lib.Lexer;

public class AriTokensTest {
  private Lexer createLexer(String str) {
    return AriTokenData.getStringLexer(str);
  }

  @Test
  public void testLexSimpleIdentifier() throws LexerException {
    Lexer lexer = createLexer("myfun");
    assertTrue(lexer.nextToken().toString().equals("1:1: myfun (IDENTIFIER)"));
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testSpecialIdentifier() throws LexerException {
    Lexer lexer = createLexer("|abc \n def| ");
    assertTrue(lexer.nextToken().toString().equals("1:1: |abc \n def| (IDENTIFIER)"));
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testDigitsAndSpecialCharacters() throws LexerException {
    Lexer lexer = createLexer("a1^%!2@>9 &45 -");
    assertTrue(lexer.nextToken().toString().equals("1:1: a1^%!2@>9 (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals("1:11: &45 (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals("1:15: - (IDENTIFIER)"));
  }

  @Test
  public void testIdentifierCannotStartWithDigit() throws LexerException {
    Lexer lexer = createLexer("1ab3");
    assertThrows(LexerException.class, () -> lexer.nextToken());
    assertTrue(lexer.nextToken().toString().equals("1:2: ab3 (IDENTIFIER)"));
  }

  @Test
  public void testLexIllegalIdentifier() throws LexerException {
    Lexer lexer = createLexer(" #");
    assertThrows(LexerException.class, () -> lexer.nextToken());
  }

  @Test
  public void testIdentifierCanStartWithArrow() throws LexerException {
    Lexer lexer = createLexer("->c->ab->a");
    assertTrue(lexer.nextToken().toString().equals("1:1: ->c->ab->a (IDENTIFIER)"));
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexComments() throws LexerException {
    Lexer lexer = createLexer("a b\nc ; d e \n f ;g");
    assertTrue(lexer.nextToken().toString().equals("1:1: a (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals("1:3: b (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals("2:1: c (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals("3:2: f (IDENTIFIER)"));
    assertTrue(lexer.nextToken().isEof());
  }

  private void verifyThrows(Lexer lexer, String message) {
    try { lexer.nextToken(); }
    catch (LexerException e) {
      assertTrue(e.getMessage().equals(message));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testUnterminatedLongIdentifier() throws LexerException {
    Lexer lexer = createLexer("hello|thing");
    assertTrue(lexer.nextToken().toString().equals("1:1: hello (IDENTIFIER)"));
    verifyThrows(lexer, "1:12: Unexpected end of input while reading long token started at 1:6.");
  }

  @Test
  public void testIllegalEscapeInIdentifier() throws LexerException {
    Lexer lexer = createLexer("hello | this is me\ntrying to escape\\| did it work?|bing");
    assertTrue(lexer.nextToken().toString().equals("1:1: hello (IDENTIFIER)"));
    verifyThrows(lexer,
      "2:17: Unexpected token: \\.  Not allowed in long token IDENTIFIER (started at 1:7).");
    assertTrue(lexer.nextToken().toString().equals("2:18: | did it work?| (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals("2:33: bing (IDENTIFIER)"));
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testAllBasicTokens() throws LexerException {
    Lexer lexer = createLexer("(format sort) fun\n rule -> rules ->a?+-@$%^&*b");
    assertTrue(lexer.nextToken().toString().equals("1:1: ( (BRACKETOPEN)"));
    assertTrue(lexer.nextToken().toString().equals("1:2: format (FORMAT)"));
    assertTrue(lexer.nextToken().toString().equals("1:9: sort (SORT)"));
    assertTrue(lexer.nextToken().toString().equals("1:13: ) (BRACKETCLOSE)"));
    assertTrue(lexer.nextToken().toString().equals("1:15: fun (FUN)"));
    assertTrue(lexer.nextToken().toString().equals("2:2: rule (RULE)"));
    assertTrue(lexer.nextToken().toString().equals("2:7: -> (ARROW)"));
    assertTrue(lexer.nextToken().toString().equals("2:10: rules (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals("2:16: ->a?+-@$%^&*b (IDENTIFIER)"));
    assertTrue(lexer.nextToken().isEof());
  }
}

