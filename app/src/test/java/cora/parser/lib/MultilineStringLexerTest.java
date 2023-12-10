package cora.parser.lib;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class MultilineStringLexerTest {
  @Test
  public void testLexer() throws LexerException {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "[a-zA-Z_][a-z0-9A-Z_]*", "IDENTIFIER",
                                       "0|[1-9][0-9]*", "INTEGER",
                                       "\\s+", "WHITESPACE" });
    Lexer lexer = new MultilineStringLexer(tf, "BING \n  12\r\n31 *_a10?\n0");
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("1:1: BING (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:5:   (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:1:    (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:3: 12 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("3:1: 31 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("3:3:   (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("3:4: * (CATCHALL)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("3:5: _a10 (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("3:9: ? (CATCHALL)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("4:1: 0 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
    assertTrue(token.toString().equals("4:2:  (EOF)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
    assertTrue(token.toString().equals("5:1:  (EOF)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("5:1:  (EOF)"));
  }
}

