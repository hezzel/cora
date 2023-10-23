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

package cora.parsing.lib;

/**
 * A lexer produces Tokens from some kind of source.  When the source ends, the lexer keeps
 * producing the EOF token indefinitely.
 *
 * Lexers are designed to be used compositionally.  For example, you can have a lexer that takes an
 * existing lexer as an argument, and passes on all its tokens, but takes out nested comments.
 */
public interface Lexer {
  /**
   * Returns the next token to be handled, or EOF if all tokens from the source have already been
   * returned.  Once EOF has been returned, all subsequent tokens will also be EOF.
   *
   * If a LexerException is thrown (for instance due to an error token being encountered, like an
   * unterminated string character), the lexer should still advance, so that requesting the next
   * token does not throw up an error for the same part of the file / input.
   */
  public Token nextToken() throws LexerException;
}
