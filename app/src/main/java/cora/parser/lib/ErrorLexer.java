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
 * An ErrorLexer adapts a given lexer by watching out for a certain token and throwing an error if
 * it comes up.
 */
class ErrorLexer implements Lexer {
  private Lexer _mylexer;
  private String _errorToken;
  private String _errorMessage;

  /** 
   * Set up a lexer that simply passes on tokens from the given lexer, except for the given token,
   * which yields an error.  Include @TEXT@ in the message to get the text of the token.
   */
  ErrorLexer(Lexer lexer, String tokenName, String message) {
    _mylexer = lexer;
    _errorToken = tokenName;
    _errorMessage = message;
  }

  /** Returns the next token or throws an exception. */
  public Token nextToken() throws LexerException {
    Token ret = _mylexer.nextToken();
    if (ret.getName().equals(_errorToken)) {
      throw new LexerException(ret, _errorMessage.replace("@TEXT@", ret.getText()));
    }
    return ret;
  }
}
