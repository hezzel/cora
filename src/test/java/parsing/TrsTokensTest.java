/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.parsing;

import org.junit.Test;
import static org.junit.Assert.*;
import cora.parsing.lib.Token;
import cora.parsing.lib.LexerException;
import cora.parsing.lib.Lexer;

public class TrsTokensTest {
  private Lexer createLexer(String str) {
    return TrsTokenData.getStringLexer(str);
  }

  private void verifyToken(Token tk, String name, String text) {
    assertTrue(tk.getName().equals(name));
    assertTrue(tk.getText().equals(text));
  }

  @Test
  public void testLexSimpleIdentifier() throws LexerException {
    Lexer lexer = createLexer("myfun");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "myfun");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexUnicodeIdentifier() throws LexerException {
    Lexer lexer = createLexer("émy∀fun");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "émy∀fun");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexWhitespaceBetweenIdentifiers() throws LexerException {
    Lexer lexer = createLexer("émy∀fun xx ∃ \nx ");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "émy∀fun");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "xx");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "∃");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "x");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexArrows() throws LexerException {
    Lexer lexer = createLexer("-> ->");
    verifyToken(lexer.nextToken(), TrsTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), TrsTokenData.ARROW, "->");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexEquality() throws LexerException {
    Lexer lexer = createLexer("==");
    verifyToken(lexer.nextToken(), TrsTokenData.EQUALITY, "==");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testExtendedEquality() throws LexerException {
    Lexer lexer = createLexer("===");
    verifyToken(lexer.nextToken(), TrsTokenData.EQUALITY, "==");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "=");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testTextWithArrows() throws LexerException {
    Lexer lexer = createLexer("ab->cd->->ef");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "ab");
    verifyToken(lexer.nextToken(), TrsTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "cd");
    verifyToken(lexer.nextToken(), TrsTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), TrsTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "ef");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testVarList() throws LexerException {
    Lexer lexer = createLexer("(VAR x  y \n  z)");
    verifyToken(lexer.nextToken(), TrsTokenData.VARSDECSTART, "(VAR");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "x");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "y");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "z");
    verifyToken(lexer.nextToken(), TrsTokenData.BRACKETCLOSE, ")");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testSignature() throws LexerException {
    Lexer lexer = createLexer("(SIG (f 2) (a 0) (h 1))");
    verifyToken(lexer.nextToken(), TrsTokenData.SIGSTART, "(SIG");
    verifyToken(lexer.nextToken(), TrsTokenData.BRACKETOPEN, "(");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "f");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "2");
    verifyToken(lexer.nextToken(), TrsTokenData.BRACKETCLOSE, ")");
  }

  @Test
  public void testComment() throws LexerException {
    Lexer lexer = createLexer("(COMMENT a b c) d");
    verifyToken(lexer.nextToken(), TrsTokenData.COMMENTSTART, "(COMMENT");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "a");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "b");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "c");
    verifyToken(lexer.nextToken(), TrsTokenData.BRACKETCLOSE, ")");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "d");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testIntegerIdentifier() throws LexerException {
    Lexer lexer = createLexer("0x1 7 54123");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "0x1");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "7");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "54123");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testMixtureWithArrowsAndEquals() throws LexerException {
    Lexer lexer = createLexer("xx-y->zb==3=9 ->aa b c->d");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "xx-y");
    verifyToken(lexer.nextToken(), TrsTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "zb");
    verifyToken(lexer.nextToken(), TrsTokenData.EQUALITY, "==");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "3=9");
    verifyToken(lexer.nextToken(), TrsTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "aa");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "b");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "c");
    verifyToken(lexer.nextToken(), TrsTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), TrsTokenData.IDENTIFIER, "d");
    assertTrue(lexer.nextToken().isEof());
  }
}

