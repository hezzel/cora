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

public class StringEditLexerTest {
  private Lexer makeLexer(String str, String[] replacements, char escape) {
    Lexer baselexer = LexerFactory.createStringLexer(new String[] {
                                       "\"([^\"]|\\\")*\"", "STRING",
                                       "\\w*", "IDENTIFIER",
                                       "\\s+", Token.SKIP,
                                    }, str);
    return new StringEditLexer(baselexer, "STRING", replacements, escape);
  }

  @Test
  public void testBasicsWithoutReplacements() throws LexerException {
    Lexer lexer = makeLexer("hello \"this is a string\"", new String[] {}, '\0');
    assertTrue(lexer.nextToken().toString().equals("1:1: hello (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals("1:7: this is a string (STRING)"));
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testReplaceNewlinesAndQuotes() throws LexerException {
    Lexer lexer = makeLexer("\"This is interesting!\\nQuote:\\n  \\\"beep\\\".\\@\"",
      new String[] { "\\n", "\n", "\\\"", "\"" }, '\0');
    assertTrue(lexer.nextToken().getText().equals("This is interesting!\nQuote:\n  \"beep\".\\@"));
  }

  @Test
  public void testReplaceNewlinesQuotesAndEscapes() throws LexerException {
    Lexer lexer = makeLexer("\"Aha\\\\!\\nQuote:\\n  \\\"beep\\\".\\\\@\"",
      new String[] { "\\n", "\n", "\\\"", "\"" }, '\\');
    assertTrue(lexer.nextToken().getText().equals("Aha\\!\nQuote:\n  \"beep\".\\@"));
  }

  @Test
  public void testReplaceWithStrayEscape() throws LexerException {
    Lexer lexer = makeLexer("\"Aha\\\\!\\nQuote:\\n  \\\"beep\\\".\\\\@\"",
      new String[] { "\\n", "\n" }, '\\');
    boolean errored = false;
    try { lexer.nextToken(); }
    catch (LexerException e) { errored = true; }
    assertTrue(errored);
    assertTrue(lexer.nextToken().getText().equals("Aha\\!\nQuote:\n  \\\"beep\\\".\\@"));
  }
}

