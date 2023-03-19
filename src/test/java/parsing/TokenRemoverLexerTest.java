package cora.parsing;

import org.junit.Test;
import static org.junit.Assert.*;

public class TokenRemoverLexerTest {
  @Test
  public void testDualRemoval() {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "[a-zA-Z_][a-z0-9A-Z_]*", "IDENTIFIER",
                                       "0|[1-9][0-9]*", "INTEGER",
                                       "\\s", "WHITESPACE",
                                       "%.*$", "COMMENT" });
    Lexer baselexer = new MultilineStringLexer(tf, "toot \n  12\r\n31 x%*_a10?\n0");
    Lexer lexer = new TokenRemoverLexer(baselexer, new String[] { "WHITESPACE", "COMMENT" });
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("1:1: toot (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:3: 12 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("3:1: 31 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("3:4: x (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("4:1: 0 (INTEGER)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
    token = lexer.nextToken();
    assertTrue(token.isEof());
  }

  @Test(expected = cora.exceptions.IllegalArgumentError.class)
  public void testCannotRemoveEof() {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "[a-zA-Z_][a-z0-9A-Z_]*", "IDENTIFIER",
                                       "0|[1-9][0-9]*", "INTEGER",
                                       "\\s", "WHITESPACE" });
    Lexer baselexer = new StringLexer(tf, "hello world");
    Lexer lexer = new TokenRemoverLexer(baselexer, new String[] { "EOF", "WHITESPACE" });
  }
}

