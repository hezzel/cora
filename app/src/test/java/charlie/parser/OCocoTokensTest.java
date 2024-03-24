/**************************************************************************************************
 Copyright 2019--2024 Cynthia Kop

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

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.parser.lib.Token;
import charlie.parser.lib.LexerException;
import charlie.parser.lib.Lexer;

public class OCocoTokensTest {
  private Lexer createLexer(String str) {
    return OCocoTokenData.getStringLexer(str);
  }

  private void verifyToken(Token tk, String name, String text) {
    assertTrue(tk.getName().equals(name));
    assertTrue(tk.getText().equals(text));
  }

  @Test
  public void testLexSimpleIdentifier() throws LexerException {
    Lexer lexer = createLexer("myfun");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "myfun");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexUnicodeIdentifier() throws LexerException {
    Lexer lexer = createLexer("émy∀fun");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "émy∀fun");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexWhitespaceBetweenIdentifiers() throws LexerException {
    Lexer lexer = createLexer("émy∀fun xx ∃ \nx ");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "émy∀fun");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "xx");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "∃");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "x");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexArrows() throws LexerException {
    Lexer lexer = createLexer("-> ->");
    verifyToken(lexer.nextToken(), OCocoTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), OCocoTokenData.ARROW, "->");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexEquality() throws LexerException {
    Lexer lexer = createLexer("==");
    verifyToken(lexer.nextToken(), OCocoTokenData.EQUALITY, "==");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testExtendedEquality() throws LexerException {
    Lexer lexer = createLexer("===");
    verifyToken(lexer.nextToken(), OCocoTokenData.EQUALITY, "==");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "=");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testTextWithArrows() throws LexerException {
    Lexer lexer = createLexer("ab->cd->->ef");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "ab");
    verifyToken(lexer.nextToken(), OCocoTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "cd");
    verifyToken(lexer.nextToken(), OCocoTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), OCocoTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "ef");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testVarList() throws LexerException {
    Lexer lexer = createLexer("(VAR x  y \n  z)");
    verifyToken(lexer.nextToken(), OCocoTokenData.VARSDECSTART, "(VAR");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "x");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "y");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "z");
    verifyToken(lexer.nextToken(), OCocoTokenData.BRACKETCLOSE, ")");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testSignature() throws LexerException {
    Lexer lexer = createLexer("(SIG (f 2) (a 0) (h 1))");
    verifyToken(lexer.nextToken(), OCocoTokenData.SIGSTART, "(SIG");
    verifyToken(lexer.nextToken(), OCocoTokenData.BRACKETOPEN, "(");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "f");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "2");
    verifyToken(lexer.nextToken(), OCocoTokenData.BRACKETCLOSE, ")");
  }

  @Test
  public void testComment() throws LexerException {
    Lexer lexer = createLexer("(COMMENT a b c) d");
    verifyToken(lexer.nextToken(), OCocoTokenData.COMMENTSTART, "(COMMENT");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "a");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "b");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "c");
    verifyToken(lexer.nextToken(), OCocoTokenData.BRACKETCLOSE, ")");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "d");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testIntegerIdentifier() throws LexerException {
    Lexer lexer = createLexer("0x1 7 54123");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "0x1");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "7");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "54123");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testMixtureWithArrowsAndEquals() throws LexerException {
    Lexer lexer = createLexer("xx-y->zb==3=9 ->aa b c->d");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "xx-y");
    verifyToken(lexer.nextToken(), OCocoTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "zb");
    verifyToken(lexer.nextToken(), OCocoTokenData.EQUALITY, "==");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "3=9");
    verifyToken(lexer.nextToken(), OCocoTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "aa");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "b");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "c");
    verifyToken(lexer.nextToken(), OCocoTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), OCocoTokenData.IDENTIFIER, "d");
    assertTrue(lexer.nextToken().isEof());
  }
}

