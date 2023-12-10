/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.parser.lib;

/**
 * A MultilineStringLexer is used to lex a string that may contain newlines, when it is given that
 * no token can span more than a single line.  Thus, we go through the lines, and set appropriate
 * positioning information for each Token we encounter.
 */
class MultilineStringLexer implements Lexer {
  private TokenFinder _tokenfinder;
  private String[] _lines;
  private int _currentLine;
  private StringLexer _currentLineLexer;

  /**
   * Set up a string lexer to tokenise the given (multiline) search string, using the tokens
   * defined in the given token finder.
   */
  MultilineStringLexer(TokenFinder finder, String search) {
    _tokenfinder = finder;
    _lines = search.split("\\R");
    _currentLine = 0;
    setupNextLexer();
  }

  /**
   * This sets _currentLineLexer up for the next line to be read.  If there is nothing left to be
   * read, then _currentLineLexer is set to null instead.
   */
  private void setupNextLexer() {
    if (_currentLine >= _lines.length) _currentLineLexer = null;
    else {
      _currentLineLexer = new StringLexer(_tokenfinder, _lines[_currentLine]);
      _currentLineLexer.setLineNumber(_currentLine + 1);
      _currentLine++;
    }
  }

  /** Returns the next token, which may be on a different line of the input. */
  public Token nextToken() throws LexerException {
    Token lastEof = null;
    while (_currentLineLexer != null) {
      Token ret = _currentLineLexer.nextToken();
      if (!ret.isEof()) return ret;
      lastEof = ret;
      setupNextLexer();
    }
    if (lastEof == null) lastEof = Token.eofToken(new ParsePosition(_currentLine + 1, 1));
    return lastEof;
  }
}
