package cora.parsing;

import java.util.Arrays;
import java.util.TreeSet;
import cora.exceptions.IllegalArgumentError;

/**
 * A TokenRemoverLexer adapts a given Lexer by removing tokens of a specific kind -- such as
 * whitespace or comment tokens.
 */
class TokenRemoverLexer implements Lexer {
  private Lexer _mylexer;
  private TreeSet<String> _remove;

  /**
   * Set up a lexer that simply passes on tokens from the given lexer, but removes the tokens whose
   * name is in the 'remove' array.
   */
  TokenRemoverLexer(Lexer lexer, String[] removable) {
    _mylexer = lexer;
    _remove = new TreeSet<String>(Arrays.asList(removable));
    if (_remove.contains(Token.EOF)) {
      throw new IllegalArgumentError("TokenRemoverLexer", "constructor",
        "You cannot exclude the EOF token, or lexing would become non-terminating!");
    }
  }

  /** Returns the next token that is not one of the removables. */
  public Token nextToken() {
    Token ret = _mylexer.nextToken();
    while (_remove.contains(ret.getName())) {
      if (ret.isEof()) return ret;    // just an extra precaution
      ret = _mylexer.nextToken();
    }
    return ret;
  }
}
