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
import cora.parsing.lib.LexerFactory;
import cora.parsing.lib.TokenQueue;

/**
 * This file defines the tokens used to lex and parse a file or string using the input format of
 * the confluence competition, http://project-coco.uibk.ac.at/problems/trs.php .
 */
public class TrsTokenData {
  /* First we define constants for all the tokens. */
  public static String IDENTIFIER     = "IDENTIFIER";
  public static String BRACKETOPEN    = "BRACKETOPEN";
  public static String BRACKETCLOSE   = "BRACKETCLOSE";
  public static String ARROW          = "ARROW";
  public static String EQUALITY       = "EQUALITY";
  public static String COMMA          = "COMMA";
  public static String VARSDECSTART   = "VARSDECSTART";
  public static String SIGSTART       = "SIGSTART";
  public static String RULESDECSTART  = "RULESDECSTART";
  public static String COMMENTSTART   = "COMMENTSTART";

  /* Next, we define the regular expressions for all tokens. */
  public static String[] tokens = new String[] {
    "([^\\s()\",|\\-=\\\\]|(-(?!>))|(=(?!=)))+" , IDENTIFIER,
      // identifiers are built from any characters other than whitespace, brackets, quotes, commas
      // and |; however, they may not contain -> or ==

    "\\("                                     , BRACKETOPEN,

    "\\)"                                     , BRACKETCLOSE,

    "->"                                      , ARROW,

    "=="                                      , EQUALITY,

    ","                                       , COMMA,

    "\\(VAR"                                  , VARSDECSTART,

    "\\(SIG"                                  , SIGSTART,

    "\\(RULES"                                , RULESDECSTART,

    "\\(COMMENT"                              , COMMENTSTART,

    "\\s"                                     , Token.SKIP,
  };

  /** Returns a TokenQueue that goes through the given file. */
  public static TokenQueue getFileLexer(String filename) throws IOException {
    return LexerFactory.createPushbackLexer(LexerFactory.createFileLexer(tokens, filename));
  }

  /** Returns a TokenQueue that goes through the given string. */
  public static TokenQueue getStringLexer(String text) {
    return LexerFactory.createPushbackLexer(LexerFactory.createStringLexer(tokens, text));
  }
}

