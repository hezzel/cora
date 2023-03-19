package cora.parsing;

import org.junit.Test;
import static org.junit.Assert.*;
import cora.exceptions.ParserError;

public class CommentRemoverLexerTest {
  private Lexer makeLexer(String str, boolean nested) {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "\\w*", "IDENTIFIER",
                                       "\\s+", "WHITESPACE",
                                       "\\([*]", "COMMENTOPEN",
                                       "[*]\\)", "COMMENTCLOSE"
                                     });
    Lexer baselexer = new MultilineStringLexer(tf, str);
    return new CommentRemoverLexer(baselexer, "COMMENTOPEN", "COMMENTCLOSE", nested);
  }

  @Test
  public void testNonNestedRemoval() {
    Lexer lexer = makeLexer("hello (* this \n is a comment (* is it not? *) world *)aa", false);
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("1:1: hello (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:6:   (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:31:   (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:32: world (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:37:   (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:38: *) (COMMENTCLOSE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:40: aa (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
  }

  @Test
  public void testNestedRemoval() {
    Lexer lexer = makeLexer("hello (* this \n is a comment (* is it not? *) worl\nd *)aa", true);
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("1:1: hello (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:6:   (WHITESPACE)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("3:5: aa (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
  }

  @Test
  public void testCannotUseEofAsComentOpen() {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "\\w*", "IDENTIFIER",
                                       "\\s+", "WHITESPACE",
                                       "\\([*]", "COMMENTOPEN",
                                       "[*]\\)", "COMMENTCLOSE"
                                     });
    Lexer baselexer = new MultilineStringLexer(tf, "hello");
    Lexer lexer = new CommentRemoverLexer(baselexer, "EOF", "COMMENTCLOSE", true);
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("1:1: hello (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
  }

  @Test(expected = ParserError.class)
  public void testCannotUseEofAsComentClose() {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "\\w*", "IDENTIFIER",
                                       "\\s+", "WHITESPACE",
                                       "\\([*]", "COMMENTOPEN",
                                       "[*]\\)", "COMMENTCLOSE"
                                     });
    Lexer baselexer = new MultilineStringLexer(tf, "hello(* bing");
    Lexer lexer = new CommentRemoverLexer(baselexer, "COMMENTOPEN", "EOF", true);
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("1:1: hello (IDENTIFIER)"));
    token = lexer.nextToken();
  }

  @Test
  public void testUnclosedBlock() {
    Lexer lexer = makeLexer("hello (* this \n is a comment \n", false);
    Token token = lexer.nextToken();    // IDENTIFIER
    token = lexer.nextToken();    // WHITESPACE
    try { token = lexer.nextToken(); }
    catch (ParserError e) {
      assertTrue(e.getMessage().equals("1:7: Parser exception on input [(*]: end of input was " +
        "reached before comment was closed"));
      return;
    }
    assertTrue(false);  // we should have returned in the catch!
  }

  @Test
  public void testUnclosedNestedBlock() {
    Lexer lexer = makeLexer("hello (* this \n is (* a comment \n", false);
    Token token = lexer.nextToken();    // IDENTIFIER
    token = lexer.nextToken();    // WHITESPACE
    try { token = lexer.nextToken(); }
    catch (ParserError e) {
      assertTrue(e.getMessage().equals("1:7: Parser exception on input [(*]: end of input was " +
        "reached before comment was closed"));
      return;
    }
    assertTrue(false);  // we should have returned in the catch!
  }
}

