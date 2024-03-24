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

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.parser.lib.Token;
import charlie.parser.lib.LexerException;
import charlie.parser.lib.Lexer;

public class ITrsTokensTest {
  private Lexer createLexer(String str) {
    return ITrsTokenData.getStringLexer(str);
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
  public void testLexSimpleIdentifier() throws LexerException {
    Lexer lexer = createLexer("myfun");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "myfun");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexUnicodeIdentifier() throws LexerException {
    Lexer lexer = createLexer("émy∀fun");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "émy∀fun");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexWhitespaceBetweenIdentifiers() throws LexerException {
    Lexer lexer = createLexer("émy∀funTRUE FALSE FALSEx TRUE \nx ");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "émy∀funTRUE");
    verifyToken(lexer.nextToken(), ITrsTokenData.FALSEHOOD, "FALSE");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "FALSEx");
    verifyToken(lexer.nextToken(), ITrsTokenData.TRUTH, "TRUE");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "x");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexArrows() throws LexerException {
    Lexer lexer = createLexer("-> ->");
    verifyToken(lexer.nextToken(), ITrsTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), ITrsTokenData.ARROW, "->");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexEquality() throws LexerException {
    Lexer lexer = createLexer("==");
    verifyToken(lexer.nextToken(), ITrsTokenData.EQUAL, "=");
    verifyToken(lexer.nextToken(), ITrsTokenData.EQUAL, "=");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testLexComments() throws LexerException {
    Lexer lexer = createLexer("a b\n c # d e \n f g");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "a");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "b");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "c");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "f");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "g");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testTextWithArrows() throws LexerException {
    Lexer lexer = createLexer("ab->c-d>->->3f");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "ab");
    verifyToken(lexer.nextToken(), ITrsTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "c");
    verifyToken(lexer.nextToken(), ITrsTokenData.MINUS, "-");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "d");
    verifyToken(lexer.nextToken(), ITrsTokenData.GREATER, ">");
    verifyToken(lexer.nextToken(), ITrsTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), ITrsTokenData.ARROW, "->");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "3f");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testVarList() throws LexerException {
    Lexer lexer = createLexer("(VAR x  y \n  z)");
    verifyToken(lexer.nextToken(), ITrsTokenData.VARSDECSTART, "(VAR");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "x");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "y");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "z");
    verifyToken(lexer.nextToken(), ITrsTokenData.BRACKETCLOSE, ")");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testComment() throws LexerException {
    Lexer lexer = createLexer("(COMMENT a b c) d");
    verifyToken(lexer.nextToken(), ITrsTokenData.COMMENTSTART, "(COMMENT");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "a");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "b");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "c");
    verifyToken(lexer.nextToken(), ITrsTokenData.BRACKETCLOSE, ")");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "d");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testIntegerIdentifier() throws LexerException {
    Lexer lexer = createLexer("0x1 7 54123 000");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "0x1");
    verifyToken(lexer.nextToken(), ITrsTokenData.INTEGER, "7");
    verifyToken(lexer.nextToken(), ITrsTokenData.INTEGER, "54123");
    verifyToken(lexer.nextToken(), ITrsTokenData.INTEGER, "000");
    assertTrue(lexer.nextToken().isEof());
  }

  @Test
  public void testAllBasicTokens() throws LexerException {
    Lexer lexer = createLexer("a+b-c*d:|:e/f%g=h>i<j>=k<==l!m!=n&&o&p|q||r,s3t:|");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "a");
    verifyToken(lexer.nextToken(), ITrsTokenData.PLUS,       "+");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "b");
    verifyToken(lexer.nextToken(), ITrsTokenData.MINUS,      "-");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "c");
    verifyToken(lexer.nextToken(), ITrsTokenData.TIMES,      "*");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "d");
    verifyToken(lexer.nextToken(), ITrsTokenData.MID,        ":|:");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "e");
    verifyToken(lexer.nextToken(), ITrsTokenData.DIV,        "/");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "f");
    verifyToken(lexer.nextToken(), ITrsTokenData.MOD,        "%");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "g");
    verifyToken(lexer.nextToken(), ITrsTokenData.EQUAL,      "=");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "h");
    verifyToken(lexer.nextToken(), ITrsTokenData.GREATER,    ">");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "i");
    verifyToken(lexer.nextToken(), ITrsTokenData.SMALLER,    "<");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "j");
    verifyToken(lexer.nextToken(), ITrsTokenData.GEQ,        ">=");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "k");
    verifyToken(lexer.nextToken(), ITrsTokenData.LEQ,        "<=");
    verifyToken(lexer.nextToken(), ITrsTokenData.EQUAL,      "=");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "l");
    verifyToken(lexer.nextToken(), ITrsTokenData.NOT,        "!");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "m");
    verifyToken(lexer.nextToken(), ITrsTokenData.UNEQUAL,    "!=");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "n");
    verifyToken(lexer.nextToken(), ITrsTokenData.AND,        "&&");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "o");
    checkExceptionOnNextToken(lexer, "1:37");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "p");
    checkExceptionOnNextToken(lexer, "1:39");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "q");
    verifyToken(lexer.nextToken(), ITrsTokenData.OR,         "||");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "r");
    verifyToken(lexer.nextToken(), ITrsTokenData.COMMA,      ",");
    verifyToken(lexer.nextToken(), ITrsTokenData.IDENTIFIER, "s3t");
    checkExceptionOnNextToken(lexer, "1:48");
    checkExceptionOnNextToken(lexer, "1:49");
    assertTrue(lexer.nextToken().isEof());
  }
}

