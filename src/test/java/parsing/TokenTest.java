package cora.parsing;

import org.junit.Test;
import static org.junit.Assert.*;

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
}

