/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.parser.lib;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;

/**
 * A FileLexer is used to lex a complete file, when it is given that no token can span over a
 * newline.  Thus, we go through all the lines in the file, and set appropriate positioning
 * information for each Token we encounter.
 */
class FileLexer implements ModeLexer {
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
    _filename = filename;
    _reader = new BufferedReader(new FileReader(filename));
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
      _currentLineLexer = new StringLexer(_tokenfinder, line + "\n");
      _currentLineLexer.setFilename(_filename);
      _currentLineLexer.setLineNumber(_currentLine);
    }
  }

  /** Returns the next token, which may be on a different line of the input. */
  public Token nextToken() throws LexerException {
    Token lastEof = null;
    while (_currentLineLexer != null) {
      Token ret = _currentLineLexer.nextToken();
      if (!ret.isEof()) return ret;
      lastEof = ret;
      try { setupNextLexer(); }
      catch (IOException e) {
        _currentLineLexer = null;
        throw new LexerException(lastEof, e.getMessage());
      }
    }
    if (lastEof == null) {
      lastEof = Token.eofToken(new ParsePosition(_filename, _currentLine + 1, 1));
    }
    return lastEof;
  }

  /** Switches the tokeniser to the given one, continuing at the current position in the file */
  public void switchMode(TokenFinder newfinder) {
    if (_currentLineLexer != null) _currentLineLexer.switchMode(newfinder);
    _tokenfinder = newfinder;
  }

  /** Returns the token finder we are currently using. */
  public TokenFinder getCurrentMode() {
    return _tokenfinder;
  }
}

