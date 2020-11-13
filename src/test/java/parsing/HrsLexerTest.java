/**************************************************************************************************
 Copyright 2020 Cynthia Kop

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
import cora.parsers.HrsLexer;

public class HrsLexerTest {
  private HrsLexer createLexer(String str) {
    return new HrsLexer(CharStreams.fromString(str));
  }

  private ArrayList<Token> tokenise(String str) {
    HrsLexer lexer = createLexer(str);
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
    assertTrue(parts.get(0).getType() == HrsLexer.IDENTIFIER);
    assertTrue(parts.get(0).getText().equals("myfun"));
  }

  @Test
  public void testLexUnicodeIdentifier() {
    ArrayList<Token> parts = tokenise("émy∀fun");
    assertTrue(parts.size() == 1);
    verifyToken(parts.get(0), HrsLexer.IDENTIFIER, "émy∀fun");
  }

  @Test
  public void testLexWhitespaceBetweenIdentifiers() {
    ArrayList<Token> parts = tokenise("émy∀fu-n x>x ∃ \nx> ");
    assertTrue(parts.size() == 4);
    verifyToken(parts.get(0), HrsLexer.IDENTIFIER, "émy∀fu-n");
    verifyToken(parts.get(3), HrsLexer.IDENTIFIER, "x>");
  }

  @Test
  public void testLexArrows() {
    ArrayList<Token> parts = tokenise("-> ->");
    assertTrue(parts.size() == 2);
    verifyToken(parts.get(0), HrsLexer.ARROW, "->");
    verifyToken(parts.get(1), HrsLexer.ARROW, "->");
  }

  @Test
  public void testEquality() {
    ArrayList<Token> parts = tokenise("===");
    assertTrue(parts.size() == 1);
    verifyToken(parts.get(0), HrsLexer.IDENTIFIER, "===");
  }

  @Test
  public void testTextWithArrows() {
    ArrayList<Token> parts = tokenise("ab->cd->->ef");
    assertTrue(parts.size() == 6);
    verifyToken(parts.get(0), HrsLexer.IDENTIFIER, "ab");
    verifyToken(parts.get(1), HrsLexer.ARROW, "->");
    verifyToken(parts.get(2), HrsLexer.IDENTIFIER, "cd");
    verifyToken(parts.get(3), HrsLexer.ARROW, "->");
    verifyToken(parts.get(4), HrsLexer.ARROW, "->");
    verifyToken(parts.get(5), HrsLexer.IDENTIFIER, "ef");
  }

  @Test
  public void testAbstraction() {
    ArrayList<Token> parts = tokenise("\\ab\\c.d");
    assertTrue(parts.size() == 6);
    verifyToken(parts.get(0), HrsLexer.LAMBDA, "\\");
    verifyToken(parts.get(1), HrsLexer.IDENTIFIER, "ab");
    verifyToken(parts.get(2), HrsLexer.LAMBDA, "\\");
    verifyToken(parts.get(3), HrsLexer.IDENTIFIER, "c");
    verifyToken(parts.get(4), HrsLexer.DOT, ".");
    verifyToken(parts.get(5), HrsLexer.IDENTIFIER, "d");
  }

  @Test
  public void testVarList() {
    ArrayList<Token> parts = tokenise("(VAR x : nat y : int -> string \n  z : ztype)");
    assertTrue(parts.size() == 13);
    verifyToken(parts.get(0), HrsLexer.VARSDECSTART, "(VAR");
    verifyToken(parts.get(1), HrsLexer.IDENTIFIER, "x");
    verifyToken(parts.get(2), HrsLexer.DECLARE, ":");
    verifyToken(parts.get(3), HrsLexer.IDENTIFIER, "nat");
    verifyToken(parts.get(4), HrsLexer.IDENTIFIER, "y");
    verifyToken(parts.get(5), HrsLexer.DECLARE, ":");
    verifyToken(parts.get(6), HrsLexer.IDENTIFIER, "int");
    verifyToken(parts.get(7), HrsLexer.ARROW, "->");
    verifyToken(parts.get(8), HrsLexer.IDENTIFIER, "string");
    verifyToken(parts.get(9), HrsLexer.IDENTIFIER, "z");
    verifyToken(parts.get(10), HrsLexer.DECLARE, ":");
    verifyToken(parts.get(11), HrsLexer.IDENTIFIER, "ztype");
    verifyToken(parts.get(12), HrsLexer.BRACKETCLOSE, ")");
  }

  @Test
  public void testSignature() {
    ArrayList<Token> parts = tokenise("(FUN f : nat g : (int -> nat) -> string)");
    assertTrue(parts.size() == 14);
    verifyToken(parts.get(0), HrsLexer.FUNSDECSTART, "(FUN");
    verifyToken(parts.get(1), HrsLexer.IDENTIFIER, "f");
    verifyToken(parts.get(2), HrsLexer.DECLARE, ":");
    verifyToken(parts.get(6), HrsLexer.BRACKETOPEN, "(");
    verifyToken(parts.get(8), HrsLexer.ARROW, "->");
    verifyToken(parts.get(11), HrsLexer.ARROW, "->");
    verifyToken(parts.get(13), HrsLexer.BRACKETCLOSE, ")");
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
    verifyToken(parts.get(0), HrsLexer.IDENTIFIER, "0x1");
    verifyToken(parts.get(1), HrsLexer.IDENTIFIER, "7");
    verifyToken(parts.get(2), HrsLexer.IDENTIFIER, "54123");
  }
}

