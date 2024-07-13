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

/**
 * A ModeLexer is a lexer that supports different modes, by switching the underlying tokeniser for
 * a different one.
 */
public interface ModeLexer extends Lexer {
  /**
   * Change the TokenFinder used by this lexer.  Any subsequent tokens will be parsed using the new
   * token finger, continuing from the current point of the input.
   */
  public void switchMode(TokenFinder newfinder);

  /** Get the current mode for this lexer (so we can switch back later). */
  public TokenFinder getCurrentMode();
}
