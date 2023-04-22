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

import java.io.IOException;

/** A LexerFactory is used to create and combine lexers, as well as TokenQueues. */
public class LexerFactory {
  /**
   * Creates a lexer that goes through the given string line by line.  Tokens cannot include a
   * newline symbol.
   */
  public static Lexer createStringLexer(String[] tokens, String text) {
    return new MultilineStringLexer(new TokenFinder(tokens), text);
  }

  /**
   * Creates a lexer that goes through the given file line by line.  Tokens cannot include a
   * newline symbol.
   */
  public static Lexer createFileLexer(String[] tokens, String filename) throws IOException {
    return new FileLexer(new TokenFinder(tokens), filename);
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
   * Adapts the given lexer to include pushback functionality.  The pushed tokens are simply the
   * first to be returned on nextToken().
   */
  public static TokenQueue createPushbackLexer(Lexer lexer) {
    return new PushbackLexer(lexer);
  }
}
