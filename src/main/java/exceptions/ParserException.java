/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.exceptions;

import org.antlr.v4.runtime.Token;

/**
 * A ParserException is simply an Exception that is used as the base class for some Exceptions that
 * only arise during parsing.
 * This is used so that parser exceptions can be caught together on user input, but more specific
 * exceptions can be easily tested for.
 */
public class ParserException extends Exception {
  private Token _token;

  /** token is allowed to be null; message is not */
  public ParserException(Token token, String message) {
    super(token == null ? message :
          token.getLine() + ":" + token.getCharPositionInLine() + ": " + message);
    _token = token;
  }

  /** returns the token at which the ParserException occurred */
  public Token queryProblematicToken() {
    return _token;
  }
}

