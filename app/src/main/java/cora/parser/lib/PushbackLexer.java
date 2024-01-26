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
 * A PushbackLexer is the most basic instantiation of a TokenQueue: this is a lexer that you can
 * push tokens to, which are returned before the next token is read.  Reading tokens is done
 * through an existing lexer which is kept internally.
 */
class PushbackLexer implements TokenQueue  {
  private LinkedList<Token> _queue;
  private Lexer _mylexer;

  /**
   * Creates a PushbackLexer which uses the given lexer for reading new tokens (the ones whihc have
   * not previously been pushed).
   */
  PushbackLexer(Lexer lexer) {
    _queue = new LinkedList<Token>();
    _mylexer = lexer;
  }

  /**
   * Returns either the next token that was pushed and not yet returned, if any, or reads a new
   * token from the internal lexer.
   */
  public Token nextToken() throws LexerException {
    if (_queue.isEmpty()) return _mylexer.nextToken();
    return _queue.pop();
  }

  /** Puts the given token on the queue, to be returned by nextToken() */
  public void push(Token token) {
    _queue.push(token);
  }
}
