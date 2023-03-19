package cora.parsing;

import cora.exceptions.IllegalArgumentError;
import cora.exceptions.ParserError;

/**
 * A CommentRemoverLexer adapts a given Lexer by removing comments of the form
 * COMMENTOPEN...COMMENTCLOSE, which are not represented by a single token (for example because
 * they may span more than one line).  It supports both nested comments and non-nested comments.
 */
class CommentRemoverLexer implements Lexer {
  private Lexer _mylexer;
  private String _commentOpenString;
  private String _commentCloseString;
  private boolean _allowNesting;

  /** 
   * Set up a lexer that simply passes on tokens from the given lexer, but when it encounters
   * commentOpen skips over it and anything until commentClose (these are both token names, not
   * strings!).
   * If "nested" is true, then commentOpen tokens within a comment block are also recognised, and
   * must be closed before the whole block is considered closed.
   */
  CommentRemoverLexer(Lexer lexer, String commentOpen, String commentClose, boolean nested) {
    _mylexer = lexer;
    _commentOpenString = commentOpen;
    _commentCloseString = commentClose;
    _allowNesting = nested;
  }

  /** Returns the next token that is not within a comment block. */
  public Token nextToken() {
    Token ret = _mylexer.nextToken();
    while (!ret.isEof() && ret.getName().equals(_commentOpenString)) {
      int opened = 1;
      while (opened > 0) {
        Token tok = _mylexer.nextToken();
        if (tok.isEof()) {
          throw new ParserError(ret.getPosition(), ret.getText(),
            "end of input was reached before comment was closed");
        }
        if (tok.getName().equals(_commentCloseString)) opened--;
        else if (tok.getName().equals(_commentOpenString) && _allowNesting) opened++;
      }
      ret = _mylexer.nextToken();
    }
    return ret;
  }
}
