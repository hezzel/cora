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

package charlie.solvesmt;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.parser.lib.*;

public class SmtTokensTest {
  private Lexer createLexer(String str) {
    return SmtTokenData.getStringLexer(str);
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
  public void testAll() throws LexerException {
    Lexer lexer = createLexer("a\n(   C ; c d\ne )");
    verifyToken(lexer.nextToken(), SmtTokenData.IDENTIFIER, "a");
    verifyToken(lexer.nextToken(), SmtTokenData.BRACKETOPEN, "(");
    verifyToken(lexer.nextToken(), SmtTokenData.IDENTIFIER, "C");
    verifyToken(lexer.nextToken(), SmtTokenData.IDENTIFIER, "e");
    verifyToken(lexer.nextToken(), SmtTokenData.BRACKETCLOSE, ")");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testString() throws LexerException {
    Lexer lexer = createLexer("a\"b c\nd \"\"e\" f \"gh\"");
    verifyToken(lexer.nextToken(), SmtTokenData.IDENTIFIER, "a");
    verifyToken(lexer.nextToken(), SmtTokenData.STRING, "b c\nd \"e");
    verifyToken(lexer.nextToken(), SmtTokenData.IDENTIFIER, "f");
    verifyToken(lexer.nextToken(), SmtTokenData.STRING, "gh");
    assertTrue(lexer.nextToken().isEof());
  }
}

