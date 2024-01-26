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
 * A StringEditLexer is used to manipulate string tokens by turning the text into the string that
 * the user intended.
 */
class StringEditLexer extends TokenEditLexer implements Lexer {
  private String[] _replacements;
  private char _escapeChar;

  /** 
   * Set up a lexer that simply passes on tokens from the given lexer, except for tokens named
   * tokenName; there, the underlying text is adapted to remove the quotes and handle the given
   * replacements.
   * These are handled in the given order (replacements[0] is changed into replacements[1], then
   * replacements[2] into replacements[3], and so on; replacements should have an even count).
   * If escapeChar is something other than \0, then if there is any remaining occurrence of
   * escapeChar after the replacements, \\ is replaced by \ and for a single \ a LexerException is
   * thrown.  If the escapeChar is null, no LexerException will be thrown by this lexer.
   */
  StringEditLexer(Lexer lexer, String tokenname, String[] replacements, char escapeChar) {
    super(lexer, tokenname);
    _replacements = replacements;
    _escapeChar = escapeChar;
  }

  protected void modifyToken(Token token) throws LexerException {
    String txt = token.getText();
    // remove the surrounding quotes
    txt = txt.substring(1, txt.length()-1);
    // do the requested replacements
    for (int i = 1; i < _replacements.length; i += 2) {
      txt = txt.replace(_replacements[i-1], _replacements[i]);
    }
    // check that all remaining escape characters are escaped, and unescape them
    String error = null;
    if (_escapeChar != '\0') {
      for (int i = 0; i < txt.length()-1; i++) {
        if (txt.charAt(i) == _escapeChar) {
          if (txt.charAt(i+1) == _escapeChar) i++;
          else {
            error = "Unexpected escape sequence " + txt.substring(i, i+2) + " at position " +
              (i+1) + " of " + txt + ".";
            break;
          }
        }
      }
      String escapeString = Character.toString(_escapeChar);
      String doubleEscape = escapeString + escapeString;
      txt = txt.replace(doubleEscape, escapeString);
    }
    storeToken(token, 0, token.getName(), txt);
    if (error != null) throw new LexerException(token, error);
  }
}

