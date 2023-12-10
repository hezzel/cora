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

import java.util.LinkedList;

/**
 * A TokenEditLexer can be used to generate custom lexer-adapters, which look for specific kinds of
 * tokens to manipulate.
 */
abstract class TokenEditLexer implements Lexer {
  private Lexer _mylexer;
  private String _tokenName;
  private LinkedList<Token> _storedTokens;

  /**
   * Should be called by the inheriting classes to indicate a lexer we are building on top of, and
   * the kind of token that we should watch out for.  All other tokens will be passed along
   * unmodified by nextToken().
   */
  protected TokenEditLexer(Lexer lexer, String tokenName) {
    _mylexer = lexer;
    _tokenName = tokenName;
    _storedTokens = new LinkedList<Token>();
  }

  /**
   * Inheriting classes should implement this function.  This is called when a token of the kind we
   * are looking for is read from the underlying lexer.  This token is passed as an argument.  The
   * function may now call storeToken() with new token information zero or more times; the stored
   * tokens will be the next ones to be returned.  It is also allowed to throw a LexerException.
   */
  protected abstract void modifyToken(Token token) throws LexerException;

  /**
   * Implementations of modifyToken should call this function to store new tokens to be returned by
   * nextToken().  By using offset, you can create a token whose position is a number of places
   * away from the position of the base token (using offset 0 will create a token at the same
   * position as base).
   */
  protected void storeToken(Token base, int offset, String newkind, String newtext) {
    _storedTokens.add(new Token(base.getRealPosition().increasePosition(offset), newkind, newtext));
  }

  /**
   * If any tokens have been stored, this function will return the first of them.  Otherwise, it
   * will ask the stored lexer for its next token.  If that token is not the one we are looking out
   * for, it is returned unmodified; but if it is, then modifyToken() is called with that token.
   * If this stores at least one token, the first is returned; otherwise, nextToken() is called
   * again until we have something to return.
   */
  public Token nextToken() throws LexerException {
    while (true) {
      if (!_storedTokens.isEmpty()) return _storedTokens.removeFirst();
      Token token = _mylexer.nextToken();
      if (!token.getName().equals(_tokenName)) return token;
      modifyToken(token);
    }
  }
}

