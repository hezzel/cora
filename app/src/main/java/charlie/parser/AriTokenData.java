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

package charlie.parser;

import java.io.IOException;
import charlie.parser.lib.*;

/**
 * This file defines the tokens used to lex and parse a file or string using the higher-order
 * ARI format.
 */
public class AriTokenData {
  public static String FORMAT         = "FORMAT";
  public static String SORT           = "SORT";
  public static String FUN            = "FUN";
  public static String RULE           = "RULE";
  public static String LAMBDA         = "LAMBDA";
  public static String IDENTIFIER     = "IDENTIFIER";
  public static String BRACKETOPEN    = "BRACKETOPEN";
  public static String BRACKETCLOSE   = "BRACKETCLOSE";
  public static String ARROW          = "ARROW";

  private static String _letter = "[a-z]|[A-Z]";
  private static String _legalchar = "~|!|@|\\$|%|\\^|&|\\*|_|-|\\+|=|<|>|\\.|\\?|\\/";
  private static String _digit = "[0-9]";

  /* Next, we define the regular expressions for all tokens. */
  private static String[] tokens = new String[] {
    "format"                                , FORMAT,
    "sort"                                  , SORT,
    "fun"                                   , FUN,
    "rule"                                  , RULE,
    "lambda"                                , LAMBDA,
    "\\|"                                   , "BAR",
    "->"                                    , ARROW,
    "(" + _letter + "|" + _legalchar + ")(" + _letter + "|" + _legalchar + "|" + _digit + ")*"
                                            , IDENTIFIER,
    "\\("                                   , BRACKETOPEN,
    "\\)"                                   , BRACKETCLOSE,
    "\\s"                                   , Token.SKIP,
    ";.*$"                                  , Token.SKIP,
  };

  private static Lexer updateLexer(ChangeableLexer mylexer) {
    Lexer lexer = LexerFactory.createLongTokenLexer(mylexer, "BAR", "[^|\\\\]", "\\|", IDENTIFIER);
    lexer = LexerFactory.createErrorLexer(lexer, Token.CATCHALL,
      "Unexpected symbol: @TEXT@. This symbol is not permitted in an ARI input file.");
    return lexer;
  }

  public static Lexer getStringLexer(String str) {
    return updateLexer(LexerFactory.createStringLexer(tokens, str));
  }

  public static Lexer getFileLexer(String filename) throws IOException {
    return updateLexer(LexerFactory.createFileLexer(tokens, filename));
  }
}

