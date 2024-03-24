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
 * A CommentRemoverLexer adapts a given Lexer by removing comments of the form
 * COMMENTOPEN...COMMENTCLOSE, which are not represented by a single token (for example because
 * they may span more than one line).  It supports both nested comments and non-nested comments.
 */
class CommentRemoverLexer implements Lexer {
  private Lexer _mylexer;
  private String _commentOpenString;
  private String _commentCloseString;
  private boolean _allowNesting;

  /** 
   * Set up a lexer that simply passes on tokens from the given lexer, but when it encounters
   * commentOpen skips over it and anything until commentClose (these are both token names, not
   * strings!).
   * If "nested" is true, then commentOpen tokens within a comment block are also recognised, and
   * must be closed before the whole block is considered closed.
   */
  CommentRemoverLexer(Lexer lexer, String commentOpen, String commentClose, boolean nested) {
    _mylexer = lexer;
    _commentOpenString = commentOpen;
    _commentCloseString = commentClose;
    _allowNesting = nested;
  }

  /** Returns the next token that is not within a comment block. */
  public Token nextToken() throws LexerException {
    Token ret = _mylexer.nextToken();
    while (!ret.isEof() && ret.getName().equals(_commentOpenString)) {
      int opened = 1;
      while (opened > 0) {
        Token tok = _mylexer.nextToken();
        if (tok.isEof()) {
          throw new LexerException(ret,
            "end of input was reached before comment [" + ret.getText() + "] was closed");
        }
        if (tok.getName().equals(_commentCloseString)) opened--;
        else if (tok.getName().equals(_commentOpenString) && _allowNesting) opened++;
      }
      ret = _mylexer.nextToken();
    }
    if (ret.getName().equals(_commentCloseString)) {
      throw new LexerException(ret,
        "unexpected comment-close token [" + ret.getText() + "] when no comment was open!");
    }
    return ret;
  }
}
