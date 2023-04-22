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
 * A ParserError may arise during parsing, but really should not: this happens if something
 * unexpected occurs in the ParseTree that has not been handled properly in the code, such as
 * changes in the lexer/parser that have not been properly updated along in the input reader.
 */
public class ParserError extends Error {
  private String _text;

  public ParserError(int line, int pos, String text, String message) {
    super(line + ":" + pos + ": Parser exception on input [" + text + "]: " + message);
    _text = text;
  }

  public ParserError(Token token, String text, String message) {
    super(token.getLine() + ":" + token.getCharPositionInLine() + ": Parser exception on input [" +
      text + "]: " + message);
    _text = text;
  }

  public String getProblematicInput() {
    return _text;
  }
}

