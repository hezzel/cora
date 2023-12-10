package cora.parser.lib;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class TokenTest {
  @Test
  public void testToken() {
    ParsePosition position = new ParsePosition("test.trs", 3, 9);
    Token token = new Token(position, "IDENTIFIER", "counter");
    assertFalse(token.isEof());
    assertTrue(token.getName().equals("IDENTIFIER"));
    assertTrue(token.getText().equals("counter"));
    assertTrue(token.getPosition().equals(position.toString()));
    assertTrue(token.toString().equals("test.trs:3:9: counter (IDENTIFIER)"));
  }

  @Test
  public void testEof() {
    ParsePosition position = new ParsePosition("test.trs", 4, 7);
    Token token = Token.eofToken(position);
    assertTrue(token.isEof());
    assertTrue(token.getName().equals("EOF"));
    assertTrue(token.getText().equals(""));
    assertTrue(token.getPosition().equals(position.toString()));
    assertTrue(token.toString().equals("test.trs:4:7:  (EOF)"));
  }

  @Test
  public void testBefore() {
    ParsePosition pos1 = new ParsePosition("test.trs", 1, 2);
    ParsePosition pos2 = new ParsePosition("test.trs", 1, 2);
    ParsePosition pos3 = new ParsePosition("test.trs", 2, 1);
    Token tok1 = new Token(pos1, "IDENTIFIER", "a");
    Token tok2 = new Token(pos2, "IDENTIFIER", "a");
    Token tok3 = new Token(pos3, "IDENTIFIER", "a");
    assertFalse(tok1.before(tok2));
    assertTrue(tok1.before(tok3));
  }

  @Test
  public void testUpdate() {
    ParsePosition position = new ParsePosition("test.trs", 3, 9);
    Token tok1 = new Token(position, "IDENTIFIER", "counter");
    Token tok2 = tok1.updateText("tree");
    assertTrue(tok1.toString().equals("test.trs:3:9: counter (IDENTIFIER)"));
    assertTrue(tok2.toString().equals("test.trs:3:9: tree (IDENTIFIER)"));
  }
}

