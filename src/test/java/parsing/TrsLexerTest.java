/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

import org.junit.Test;
import static org.junit.Assert.*;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Token;
import java.util.ArrayList;
import cora.parsers.TrsLexer;

public class TrsLexerTest {
  private TrsLexer createLexer(String str) {
    return new TrsLexer(CharStreams.fromString(str));
  }

  private ArrayList<Token> tokenise(String str) {
    TrsLexer lexer = createLexer(str);
    ArrayList<Token> ret = new ArrayList<Token>();
    while (true) {
      Token tk = lexer.nextToken();
      if (tk.getType() == Token.EOF) break;
      ret.add(tk);
    }
    return ret;
  }

  private void verifyToken(Token tk, int kind, String text) {
    assertTrue(tk.getType() == kind);
    assertTrue(tk.getText().equals(text));
  }

  @Test
  public void testLexSimpleIdentifier() {
    ArrayList<Token> parts = tokenise("myfun");
    assertTrue(parts.size() == 1);
    assertTrue(parts.get(0).getType() == TrsLexer.IDENTIFIER);
    assertTrue(parts.get(0).getText().equals("myfun"));
  }

  @Test
  public void testLexUnicodeIdentifier() {
    ArrayList<Token> parts = tokenise("émy∀fun");
    assertTrue(parts.size() == 1);
    verifyToken(parts.get(0), TrsLexer.IDENTIFIER, "émy∀fun");
  }

  @Test
  public void testLexWhitespaceBetweenIdentifiers() {
    ArrayList<Token> parts = tokenise("émy∀fun xx ∃ \nx ");
    assertTrue(parts.size() == 4);
    verifyToken(parts.get(0), TrsLexer.IDENTIFIER, "émy∀fun");
    verifyToken(parts.get(3), TrsLexer.IDENTIFIER, "x");
  }

  @Test
  public void testLexArrows() {
    ArrayList<Token> parts = tokenise("-> ->");
    assertTrue(parts.size() == 2);
    verifyToken(parts.get(0), TrsLexer.ARROW, "->");
    verifyToken(parts.get(1), TrsLexer.ARROW, "->");
  }

  @Test
  public void testLexEquality() {
    ArrayList<Token> parts = tokenise("==");
    assertTrue(parts.size() == 1);
    verifyToken(parts.get(0), TrsLexer.EQUALITY, "==");
  }

  @Test
  public void testExtendedEquality() {
    ArrayList<Token> parts = tokenise("===");
    assertTrue(parts.size() == 2);
    verifyToken(parts.get(0), TrsLexer.EQUALITY, "==");
    verifyToken(parts.get(1), TrsLexer.IDENTIFIER, "=");
  }

  @Test
  public void testTextWithArrows() {
    ArrayList<Token> parts = tokenise("ab->cd->->ef");
    assertTrue(parts.size() == 6);
    verifyToken(parts.get(0), TrsLexer.IDENTIFIER, "ab");
    verifyToken(parts.get(1), TrsLexer.ARROW, "->");
    verifyToken(parts.get(2), TrsLexer.IDENTIFIER, "cd");
    verifyToken(parts.get(3), TrsLexer.ARROW, "->");
    verifyToken(parts.get(4), TrsLexer.ARROW, "->");
    verifyToken(parts.get(5), TrsLexer.IDENTIFIER, "ef");
  }

  @Test
  public void testVarList() {
    ArrayList<Token> parts = tokenise("(VAR x  y \n  z)");
    assertTrue(parts.size() == 5);
    verifyToken(parts.get(0), TrsLexer.VARSDECSTART, "(VAR");
    verifyToken(parts.get(1), TrsLexer.IDENTIFIER, "x");
    verifyToken(parts.get(2), TrsLexer.IDENTIFIER, "y");
    verifyToken(parts.get(3), TrsLexer.IDENTIFIER, "z");
    verifyToken(parts.get(4), TrsLexer.BRACKETCLOSE, ")");
  }

  @Test
  public void testSignature() {
    ArrayList<Token> parts = tokenise("(SIG (f 2) (a 0) (h 1))");
    assertTrue(parts.size() == 14);
    verifyToken(parts.get(0), TrsLexer.SIGSTART, "(SIG");
    verifyToken(parts.get(1), TrsLexer.BRACKETOPEN, "(");
    verifyToken(parts.get(2), TrsLexer.IDENTIFIER, "f");
    verifyToken(parts.get(3), TrsLexer.IDENTIFIER, "2");
    verifyToken(parts.get(4), TrsLexer.BRACKETCLOSE, ")");
    verifyToken(parts.get(13), TrsLexer.BRACKETCLOSE, ")");
  }

  @Test
  public void testSafeComment() {
    ArrayList<Token> parts = tokenise("(COMMENT a b c) d");
    assertTrue(parts.size() == 1);
    verifyToken(parts.get(0), TrsLexer.IDENTIFIER, "d");
  }

  @Test
  public void testCommentWithBrackets() {
    ArrayList<Token> parts = tokenise("(COMMENT a b c) d)");
    assertTrue(parts.size() == 0);
  }

  @Test
  public void testIntegerIdentifier() {
    ArrayList<Token> parts = tokenise("0x1 7 54123");
    assertTrue(parts.size() == 3);
    verifyToken(parts.get(0), TrsLexer.IDENTIFIER, "0x1");
    verifyToken(parts.get(1), TrsLexer.IDENTIFIER, "7");
    verifyToken(parts.get(2), TrsLexer.IDENTIFIER, "54123");
  }

  @Test
  public void testMixtureWithArrowsAndEquals() {
    ArrayList<Token> parts = tokenise("xx-y->zb==3=9 ->aa b c->d");
    assertTrue(parts.size() == 11);
    verifyToken(parts.get(0), TrsLexer.IDENTIFIER, "xx-y");
    verifyToken(parts.get(1), TrsLexer.ARROW, "->");
    verifyToken(parts.get(2), TrsLexer.IDENTIFIER, "zb");
    verifyToken(parts.get(3), TrsLexer.EQUALITY, "==");
    verifyToken(parts.get(4), TrsLexer.IDENTIFIER, "3=9");
    verifyToken(parts.get(5), TrsLexer.ARROW, "->");
    verifyToken(parts.get(6), TrsLexer.IDENTIFIER, "aa");
    verifyToken(parts.get(7), TrsLexer.IDENTIFIER, "b");
    verifyToken(parts.get(8), TrsLexer.IDENTIFIER, "c");
    verifyToken(parts.get(9), TrsLexer.ARROW, "->");
    verifyToken(parts.get(10), TrsLexer.IDENTIFIER, "d");
  }
}

