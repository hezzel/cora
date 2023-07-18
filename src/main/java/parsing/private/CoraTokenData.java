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

package cora.parsing;

import java.io.IOException;
import cora.parsing.lib.Token;
import cora.parsing.lib.Lexer;
import cora.parsing.lib.LexerException;
import cora.parsing.lib.LexerFactory;
import cora.parsing.lib.TokenEditLexer;
import cora.parsing.lib.TokenQueue;

/**
 * This file defines the tokens used to lex and parse a file or string using Cora's internal
 * input format.
 */
public class CoraTokenData {
  /* First we define constants for all the tokens. */
  public static String IDENTIFIER     = "IDENTIFIER";
  public static String BRACKETOPEN    = "BRACKETOPEN";
  public static String BRACKETCLOSE   = "BRACKETCLOSE";
  public static String BRACEOPEN      = "BRACEOPEN";
  public static String BRACECLOSE     = "BRACECLOSE";
  public static String METAOPEN       = "METAOPEN";
  public static String METACLOSE      = "METACLOSE";
  public static String COMMA          = "COMMA";
  public static String COLON          = "COLON";
  public static String DECLARE        = "DECLARE";
  public static String LAMBDA         = "LAMBDA";
  public static String DOT            = "DOT";
  public static String ARROW          = "ARROW";
  public static String RULEARROW      = "RULEARROW";
  public static String TYPEARROW      = "TYPEARROW";
  public static String STRING         = "STRING";

  /* Next, we define the regular expressions for all tokens. */
  public static String[] tokens = new String[] {
    "([^\\s()\\[\\]⟨⟩\\{\\}\",:λ\\.\\*\\\\\\.→⇒/-]|(-(?!>))|(/(?!\\*))|(\\*(?!/)))+" , IDENTIFIER,
      // identifiers are built from any characters other than whitespace, brackets (of any kind),
      // braces, quotes, commas, colons, lambda, backslash, dot, or unicode arrows
      // they also may not contain -> or /* or */

    "\\("                                     , BRACKETOPEN,
    "\\)"                                     , BRACKETCLOSE,
    "\\{"                                     , BRACEOPEN,
    "\\}"                                     , BRACECLOSE,
    "⟨"                                       , METAOPEN,
    "⟩"                                       , METACLOSE,
    "\\["                                     , METAOPEN,
    "\\]"                                     , METACLOSE,
    ","                                       , COMMA,
    ":"                                       , COLON,
    "::"                                      , DECLARE,
    "λ"                                       , LAMBDA,
    "\\\\"                                    , LAMBDA,
    "\\."                                     , DOT,
    "->"                                      , ARROW,
    "→"                                       , RULEARROW,
    "⇒"                                       , TYPEARROW,
    "/\\*"                                    , "COMMENTOPEN",
    "\\*/"                                    , "COMMENTCLOSE",
    "\"([^\"\\\\]|(\\\\.))*\""                , STRING,
    "\"([^\"\\\\]|(\\\\.))*$"                 , "PARTIALSTRING",
    "\"([^\"\\\\]|(\\\\.))*\\\\$"             , "PARTIALSTRING",
    "\\s"                                     , Token.SKIP,
  };

  private static TokenQueue combineLexer(Lexer lexer) {
    lexer = LexerFactory.createNestedCommentRemoverLexer(lexer, "COMMENTOPEN", "COMMENTCLOSE");
    lexer = new PartialStringWarner(lexer);
    lexer = LexerFactory.createStringEditLexer(lexer, STRING,
      new String[] {  "\\n", "\n", "\\\"", "\"" }, '\\');
    return LexerFactory.createPushbackLexer(lexer);
  }

  /** Returns a TokenQueue that goes through the given file. */
  public static TokenQueue getFileLexer(String filename) throws IOException {
    return combineLexer(LexerFactory.createFileLexer(tokens, filename));
  }

  /** Returns a TokenQueue that goes through the given string. */
  public static TokenQueue getStringLexer(String text) {
    return combineLexer(LexerFactory.createStringLexer(tokens, text));
  }

  /**
   * Helper class used to throw an error when encountering incomplete strings, but afterwards
   * process them as proper string constants.
   */
  private static class PartialStringWarner extends TokenEditLexer {
    PartialStringWarner(Lexer lexer) { super(lexer, "PARTIALSTRING"); }
    protected void modifyToken(Token token) throws LexerException {
      storeToken(token, 0, STRING, token.getText() + "\"");
      throw new LexerException(token, "Incomplete string constant (ended by end of line).");
    }
  }
}

