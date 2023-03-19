package cora.parsing;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import cora.exceptions.ParserError;

/**
 * A FileLexer is used to lex a complete file, when it is given that no token can span over a
 * newline.  Thus, we go through all the lines in the file, and set appropriate positioning
 * information for each Token we encounter.
 */
class FileLexer implements Lexer {
  private TokenFinder _tokenfinder;
  private BufferedReader _reader;
  private StringLexer _currentLineLexer;
  private String _filename;
  private int _currentLine;

  /**
   * Set up a file lexer to tokenise the given file, using the tokens defined in the given token
   * finder.
   */
  FileLexer(TokenFinder finder, String filename) throws IOException {
    _tokenfinder = finder;
    _reader = new BufferedReader(new FileReader("sample.txt"));
    _currentLine = 0;
    setupNextLexer();
  }

  /**
   * This sets _currentLineLexer up for the next line to be read.  If there is nothing left to be
   * read, then _currentLineLexer is set to null instead.
   */
  private void setupNextLexer() throws IOException {
    _currentLine++;
    String line = _reader.readLine();
    if (line == null) _currentLineLexer = null;
    else {
      _currentLineLexer = new StringLexer(_tokenfinder, line);
      _currentLineLexer.setFilename(_filename);
      _currentLineLexer.setLineNumber(_currentLine);
    }
  }

  /** Returns the next token, which may be on a different line of the input. */
  public Token nextToken() {
    Token lastEof = null;
    while (_currentLineLexer != null) {
      Token ret = _currentLineLexer.nextToken();
      if (!ret.isEof()) return ret;
      lastEof = ret;
      try { setupNextLexer(); }
      catch (IOException e) {
        _currentLineLexer = null;
        throw new ParserError(lastEof.getPosition(), "", e.getMessage());
      }
    }
    if (lastEof == null) lastEof = Token.eofToken(new ParsePosition(_currentLine + 1, 1));
    return lastEof;
  }
}
