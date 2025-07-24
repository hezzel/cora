/**************************************************************************************************
 Copyright 2024--2025 Cynthia Kop

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

/**
 * A LongTokenLexer adapts a given Lexer to support multiline tokens of the form OPEN MIDDLE*
 * CLOSE, where newlines may appear before or after any of the MIDDLE parts.  This requires the
 * original lexer to have a token for OPEN, but not for MIDDLE or CLOSE.
 */
class LongTokenLexer implements ChangeableLexer {
  private ChangeableLexer _mylexer;
  private String _openTokenName;
  private TokenFinder _myTokens;
  private String _resultName;

  /**
   * Set up a lexer that simply passes on tokens from the given lexer, but when it encounters a
   * token whose name is tokenOpen, then it switches mode, reads middleExp until closeExp is
   * encountered, appends the results together (including newlines), and returns the result as a
   * single token.  Please note that:
   * - tokenOpen is the NAME of a token in the original lexer
   * - middleExp and closeExp are REGULAR EXPRESSIONS, which do not have to be in lexer
   * - myName is a token name: the name of the returned token
   * - myName is allowed to be Token.SKIP; in this case, we pass over all instances of
   *   this token and simply return the next one (but in this case, consider using the
   *   CommentRemoverLexer instead)
   */
  LongTokenLexer(ChangeableLexer lexer, String tokenOpen, String middleExp, String closeExp,
                 String myName) {
    _mylexer = lexer;
    _openTokenName = tokenOpen;
    _myTokens = new TokenFinder(new String[] { closeExp, "LONGTOKENCLOSE",
                                               middleExp, "LONGTOKENMIDDLE" });
    _resultName = myName;
  }

  /**
   * Returns the next token, including the long token.
   * If we encounter the opening token for the long token, but this is NOT followed by MIDDLE*
   * CLOSE, then a LexerException is thrown.  In the next step, we will then continue after the
   * last OPEN or MIDDLE token that we were able to read.
   */
  public Token nextToken() throws LexerException {
    Token ret = _mylexer.nextToken();
    if (ret.isEof()) return ret;
    if (!ret.getName().equals(_openTokenName)) return ret;
    TokenFinder backup = _mylexer.getCurrentTokenData();
    _mylexer.changeTokenData(_myTokens);
    StringBuilder txt = new StringBuilder(ret.getText());

    while (true) {
      Token token;
      try { token = _mylexer.nextToken(); }
      catch (LexerException e) {
        _mylexer.changeTokenData(backup);
        throw new LexerException(e.queryToken(), e.queryMainMessage() + " (long token " +
          _resultName + " started at " + ret.getPosition() + " not finished)");
      }
      txt.append(token.getText());
      if (token.getName().equals("LONGTOKENCLOSE")) break;
      if (token.isEof()) {
        _mylexer.changeTokenData(backup);
        throw new LexerException(token, "Unexpected end of input while reading long token " +
          "started at " + ret.getPosition() + ".");
      }
      if (!token.getName().equals("LONGTOKENMIDDLE")) {
        _mylexer.changeTokenData(backup);
        throw new LexerException(token, "Unexpected token: " + token.getText() + ".  Not allowed " +
          "in long token " + _resultName + " (started at " + ret.getPosition() + ").");
      }
    }

    _mylexer.changeTokenData(backup);
    if (_resultName.equals(Token.SKIP)) return nextToken();
    return ret.samePositionToken(_resultName, txt.toString());
  }

  public void changeTokenData(TokenFinder finder) {
    _mylexer.changeTokenData(finder);
  }

  public TokenFinder getCurrentTokenData() {
    return _mylexer.getCurrentTokenData();
  }
}
