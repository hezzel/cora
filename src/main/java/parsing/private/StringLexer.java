package cora.parsing;

/**
 * A StringLexer takes a single string of input, and tokenises it.  When the source ends, the lexer
 * keeps producing the EOF token indefinitely.  The string is not required to be a single line
 * (there are allowed to be newlines), though this is a common use.
 */
class StringLexer implements Lexer {
  private TokenFinder _tokenfinder;
  private String _mystring;
  private String _filename;
  private int _lineno;
  private int _linepos;
  private int _start;

  /**
   * Set up a string lexer to tokenise the given search string, using the tokens defined in the
   * given token finder.
   */
  StringLexer(TokenFinder finder, String search) {
    _tokenfinder = finder;
    _mystring = search;
    _filename = null;
    _lineno = 0;
    _linepos = 1;
    _start = 0;
  }

  /**
   * For use in error messages: if you set the file name and line number, then any token produced
   * by this lexer will be marked as positioned in the given file and line.  Do not set the file
   * name without the line number, as this will give a silly position description.
   */
  void setFilename(String filename) {
    _filename = filename;
  }

  /**
   * For use in error messages: if you set the line number, then any token produced by this lexer
   * will be marked as positioned on the given line.
   */
  void setLineNumber(int number) {
    _lineno = number;
  }

  /**
   * For use in error messages: if you set the position offset to N, then any token produced by
   * this lexer will have its position increased by the given offset.
   */
  void setPositionOffset(int offset) {
    _linepos = offset;
  }

  /**
   * Returns the next token that was read, or EOF if all tokens from the source have already been
   * returned.
   */
  public Token nextToken() {
    ParsePosition pos = new ParsePosition(_filename, _lineno, _linepos + _start);
    Token ret = _tokenfinder.matchStart(_mystring, _start, pos);
    if (ret == null) return Token.eofToken(pos);
    _start += ret.getText().length();
    return ret;
  }
}
