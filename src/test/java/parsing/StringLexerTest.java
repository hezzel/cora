package cora.parsing;

import org.junit.Test;
import static org.junit.Assert.*;

public class StringLexerTest {
  @Test
  public void testLexerWithoutFileOrLine() {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "[a-zA-Z_][a-z0-9A-Z_]*", "IDENTIFIER",
                                       "0|[1-9][0-9]*", "INTEGER",
                                       "\\s", "WHITESPACE" });
    Lexer lexer = new StringLexer(tf, "BING  1231 *_a10?\n00	x");
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("1: BING (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("5:   (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("6:   (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("7: 1231 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("11:   (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("12: * (CATCHALL)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("13: _a10 (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("17: ? (CATCHALL)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("18: \n (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("19: 0 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("20: 0 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("21: 	 (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("22: x (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
    token = lexer.nextToken();
    assertTrue(token.isEof());
  }
}

