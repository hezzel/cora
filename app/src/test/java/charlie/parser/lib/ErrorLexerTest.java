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

public class ErrorLexerTest {
  private String checkNextError(Lexer lexer) {
    try { lexer.nextToken(); }
    catch (LexerException e) { return e.getMessage(); }
    return null;
  }

  @Test
  public void testLexerWithRemoveables() throws LexerException {
    String str = "Hello what a stuuuuuuupid and daft (daaaaft) thing this stupidity is.";
    Lexer lexer = LexerFactory.createStringLexer(new String[] {
        "stu+pid", "STUPID",
        "da+ft", "DAFT",
        "fine", "FINE",
        "\\w*", "IDENTIFIER",
        "\\s+", Token.SKIP,
      }, str);
    lexer = LexerFactory.createErrorLexer(lexer, "DAFT", "This is daft.");
    lexer = LexerFactory.createErrorLexer(lexer, "STUPID", "This is stupid: @TEXT@.");
    assertTrue(lexer.nextToken().toString().equals("1:1: Hello (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals("1:7: what (IDENTIFIER)"));
    assertTrue(lexer.nextToken().toString().equals("1:12: a (IDENTIFIER)"));
    assertTrue(checkNextError(lexer).equals("1:14: This is stupid: stuuuuuuupid."));
    assertTrue(lexer.nextToken().toString().equals("1:27: and (IDENTIFIER)"));
    assertTrue(checkNextError(lexer).equals("1:31: This is daft."));
    assertTrue(lexer.nextToken().toString().equals("1:36: ( (CATCHALL)"));
    assertTrue(checkNextError(lexer).equals("1:37: This is daft."));
    assertTrue(lexer.nextToken().getName().equals("CATCHALL"));
    assertTrue(lexer.nextToken().getName().equals("IDENTIFIER"));
    assertTrue(lexer.nextToken().getName().equals("IDENTIFIER"));
    assertTrue(lexer.nextToken().getName().equals("IDENTIFIER"));
    assertTrue(lexer.nextToken().getName().equals("IDENTIFIER"));
    assertTrue(lexer.nextToken().getName().equals("CATCHALL"));
    assertTrue(lexer.nextToken().isEof());
  }
}

