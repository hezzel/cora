/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.solvesmt;

import java.io.IOException;
import charlie.parser.lib.Token;
import charlie.parser.lib.LexerFactory;
import charlie.parser.lib.TokenQueue;
import charlie.parser.lib.Lexer;

/**
 * This file defines the tokens used to lex and parse a file or string using the smtlib format.
 * We deliberately do not recognise keywords; any SMT theory is supported.
 */
class SmtTokenData {
  public static String NUMERAL        = "NUMERAL";
  public static String IDENTIFIER     = "IDENTIFIER";
  public static String BRACKETOPEN    = "BRACKETOPEN";
  public static String BRACKETCLOSE   = "BRACKETCLOSE";

  /* Next, we define the regular expressions for all tokens. */
  public static String[] tokens = new String[] {
    "0|([1-9][0-9]*)"                       , NUMERAL,
    "[^\\s();]+"                            , IDENTIFIER,
    "\\("                                   , BRACKETOPEN,
    "\\)"                                   , BRACKETCLOSE,
    "\\s"                                   , Token.SKIP,
    ";.*$"                                  , Token.SKIP,
  };

  /** Returns a TokenQueue that goes through the given file. */
  public static TokenQueue getFileLexer(String filename) throws IOException {
    Lexer lexer = LexerFactory.createFileLexer(tokens, filename);
    lexer = LexerFactory.createErrorLexer(lexer, "ILLEGAL", "Illegal token: @TEXT@.");
    return LexerFactory.createPushbackLexer(lexer);
  }

  /** Returns a TokenQueue that goes through the given string. */
  public static TokenQueue getStringLexer(String text) {
    Lexer lexer = LexerFactory.createStringLexer(tokens, text);
    lexer = LexerFactory.createErrorLexer(lexer, "ILLEGAL", "Illegal token: @TEXT@.");
    return LexerFactory.createPushbackLexer(lexer);
  }
}

