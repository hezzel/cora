package cora.parsing.lib;

import org.junit.Test;
import static org.junit.Assert.*;

public class CommentRemoverLexerTest {
  private Lexer makeLexer(String str, boolean nested) {
    Lexer baselexer = LexerFactory.createStringLexer(new String[] {
                                       "\\w*", "IDENTIFIER",
                                       "\\s+", Token.SKIP,
                                       "\\([*]", "COMMENTOPEN",
                                       "[*]\\)", "COMMENTCLOSE"
                                    }, str);
    if (nested) {
      return LexerFactory.createNestedCommentRemoverLexer(baselexer, "COMMENTOPEN", "COMMENTCLOSE");
    }
    else {
      return LexerFactory.createBasicCommentRemoverLexer(baselexer, "COMMENTOPEN", "COMMENTCLOSE");
    }
  }

  @Test
  public void testNonNestedRemoval() throws LexerException {
    Lexer lexer = makeLexer("hello (* this \n is a comment (* is it not? *) world *)aa", false);
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("1:1: hello (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:32: world (IDENTIFIER)"));
    boolean errored = false;
    try { lexer.nextToken(); }
    catch (LexerException e) {
      errored = true;
      assertTrue(e.getMessage().equals(
        "2:38: unexpected comment-close token [*)] when no comment was open!"));
    }
    assertTrue(errored);
    token = lexer.nextToken();
    assertTrue(token.toString().equals("2:40: aa (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
  }

  @Test
  public void testNestedRemoval() throws LexerException {
    Lexer lexer = makeLexer("hello (* this \n is a comment (* is it not? *) worl\nd *)aa", true);
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("1:1: hello (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("3:5: aa (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.isEof());
  }

  @Test
  public void testCannotUseEofAsComentOpen() throws LexerException {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "\\w*", "IDENTIFIER",
                                       "\\s+", "SKIP",
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

  @Test(expected = LexerException.class)
  public void testCannotUseEofAsComentClose() throws LexerException {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "\\w*", "IDENTIFIER",
                                       "\\s+", "WHITESPACE",
                                       "\\([*]", "COMMENTOPEN",
                                       "[*]\\)", "COMMENTCLOSE"
                                     });
    Lexer baselexer = new MultilineStringLexer(tf, "hello (* bing");
    Lexer lexer = new CommentRemoverLexer(baselexer, "COMMENTOPEN", "EOF", true);
    Token token = lexer.nextToken();
    assertTrue(token.toString().equals("1:1: hello (IDENTIFIER)"));
    token = lexer.nextToken();
    assertTrue(token.toString().equals("1:6:   (WHITESPACE)"));
    token = lexer.nextToken();
  }

  @Test
  public void testUnclosedBlock() throws LexerException {
    Lexer lexer = makeLexer("hello (* this \n is a comment \n", false);
    Token token = lexer.nextToken();    // IDENTIFIER
    try { token = lexer.nextToken(); }
    catch (LexerException e) {
      assertTrue(e.getMessage().equals(
        "1:7: end of input was reached before comment [(*] was closed"));
      return;
    }
    assertTrue(false);  // we should have returned in the catch!
  }

  @Test
  public void testUnclosedNestedBlock() throws LexerException {
    Lexer lexer = makeLexer("hello (* this \n is (* a comment \n", false);
    Token token = lexer.nextToken();    // IDENTIFIER
    try { token = lexer.nextToken(); }
    catch (LexerException e) {
      assertTrue(e.getMessage().equals(
        "1:7: end of input was reached before comment [(*] was closed"));
      return;
    }
    assertTrue(false);  // we should have returned in the catch!
  }
}

