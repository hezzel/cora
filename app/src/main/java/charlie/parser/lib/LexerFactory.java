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

import java.io.IOException;

/** A LexerFactory is used to create and combine lexers, as well as TokenQueues. */
public class LexerFactory {
  /**
   * Creates a lexer that goes through the given string line by line.  Tokens cannot include a
   * newline symbol.
   */
  public static ModeLexer createStringLexer(String[] tokens, String text) {
    return new MultilineStringLexer(new TokenFinder(tokens), text);
  }

  /**
   * Creates a lexer that goes through the given file line by line.  Tokens cannot include a
   * newline symbol.
   */
  public static ModeLexer createFileLexer(String[] tokens, String filename) throws IOException {
    return new FileLexer(new TokenFinder(tokens), filename);
  }

  /**
   * Creates a lexer that adapts the given lexer by setting up a long (multiline) token.  The token
   * starts when a token with name tokenOpen is encountered; then proceeds to read the expression
   * middleExp 0 or more times, until the expression closeExp is encountered; the complete string is
   * then combined into a token with name resultName.
   */
  public static ModeLexer createLongTokenLexer(ModeLexer lexer, String tokenOpen, String middleExp,
                                               String closeExp, String resultName) {
    return new LongTokenLexer(lexer, tokenOpen, middleExp, closeExp, resultName);
  }

  /**
   * Adapts the given lexer to remove any tokens between copen and cclose.
   */
  public static Lexer createBasicCommentRemoverLexer(Lexer lexer, String copen, String cclose) {
    return new CommentRemoverLexer(lexer, copen, cclose, false);
  }

  /**
   * Adapts the given lexer to remove any tokens between copen and cclose.  These tokens are viewed
   * in a NESTED way: if copen occurs again within a "comment" block, then cclose needs to occur a
   * second time before the comment is closed, etc.
   */
  public static Lexer createNestedCommentRemoverLexer(Lexer lexer, String copen, String cclose) {
    return new CommentRemoverLexer(lexer, copen, cclose, true);
  }

  /**
   * Adapts the given lexer to update the text of string tokens.
   * String tokens should have getName() return stringTokenName,.
   * The replacements are handled in the given order (replacements[0] is changed into
   * replacements[1], then replacements[2] into replacements[3], and so on; replacements should
   * have an even count).
   * If escapeChar is something other than \0, then if there is any remaining occurrence of
   * escapeChar after the replacements, \\ is replaced by \ and for a single \ a LexerException is
   * thrown.  If the escapeChar is null, no LexerException will be thrown by this lexer.
   */
  public static Lexer createStringEditLexer(Lexer lexer, String stringTokenName,
                                            String[] replacements, char escapeChar) {
    return new StringEditLexer(lexer, stringTokenName, replacements, escapeChar);
  }

  /**
   * Adapts the given lexer to throw an error when encountering a token by the given name.  To
   * include the text of the token, put @TEXT@ in the message.
   */
  public static Lexer createErrorLexer(Lexer lexer, String token, String message) {
    return new ErrorLexer(lexer, token, message);
  }

  /**
   * Adapts the given lexer to include pushback functionality.  The pushed tokens are simply the
   * first to be returned on nextToken().
   */
  public static TokenQueue createPushbackLexer(Lexer lexer) {
    return new PushbackLexer(lexer);
  }
}
