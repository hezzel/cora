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

package charlie.parser;

import java.io.IOException;
import charlie.parser.lib.Token;
import charlie.parser.lib.LexerFactory;
import charlie.parser.lib.TokenQueue;
import charlie.parser.lib.Lexer;

/**
 * This file defines the tokens used to lex and parse a file or string using the itrs format that
 * up until 2023 was used in the termination competition.
 *
 * Note that this class is NOT public, because it should not be used outside the parser package.
 * Use the ITrsParser instead.
 */
class ITrsTokenData {
  /* First we define constants for all the tokens. */
  public static String IDENTIFIER     = "IDENTIFIER";
  public static String BRACKETOPEN    = "BRACKETOPEN";
  public static String BRACKETCLOSE   = "BRACKETCLOSE";
  public static String ARROW          = "ARROW";
  public static String COMMA          = "COMMA";
  public static String MID            = "MID";
  public static String VARSDECSTART   = "VARSDECSTART";
  public static String RULESDECSTART  = "RULESDECSTART";
  public static String COMMENTSTART   = "COMMENTSTART";
  public static String INTEGER        = "INTEGER";
  public static String TRUTH          = "TRUTH";
  public static String FALSEHOOD      = "FALSEHOOD";
  public static String PLUS           = "PLUS";
  public static String MINUS          = "MINUS";
  public static String TIMES          = "TIMES";
  public static String DIV            = "DIV";
  public static String MOD            = "MOD";
  public static String EQUAL          = "EQUAL";
  public static String GREATER        = "GREATER";
  public static String SMALLER        = "SMALLER";
  public static String GEQ            = "GEQ";
  public static String LEQ            = "LEQ";
  public static String UNEQUAL        = "UNEQUAL";
  public static String NOT            = "NOT";
  public static String AND            = "AND";
  public static String OR             = "OR";

  /* Next, we define the regular expressions for all tokens. */
  public static String[] tokens = new String[] {
    "TRUE"                                    , TRUTH,
    "FALSE"                                   , FALSEHOOD,
    "[0-9]+"                                  , INTEGER,
    "@z"                                      , Token.SKIP,

    "[^\\s()\",|\\-\\+\\*/%><=!&#:\\\\]+"     , IDENTIFIER,
        // I could not find a description of the formalism, so this is just a
        // guess as to what is allowed: anything that's not (part of) one of
        // the special symbols

    "\\+"                                     , PLUS,
    "-"                                       , MINUS,
    "\\*"                                     , TIMES,
    ":\\|:"                                   , MID,
    "/"                                       , DIV,
    "%"                                       , MOD,
    "="                                       , EQUAL,
    ">"                                       , GREATER,
    "<"                                       , SMALLER,
    "!"                                       , NOT,
    ">="                                      , GEQ,
    "<="                                      , LEQ,
    "!="                                      , UNEQUAL,
    "&&"                                      , AND,
    "\\|\\|"                                  , OR, 
    "\\("                                     , BRACKETOPEN,
    "\\)"                                     , BRACKETCLOSE,
    "->"                                      , ARROW,
    ","                                       , COMMA,
    "&"                                       , "ILLEGAL",
    "\\|"                                     , "ILLEGAL",
    ":"                                       , "ILLEGAL",
    "\\(VAR"                                  , VARSDECSTART,
    "\\(RULES"                                , RULESDECSTART,
    "\\(COMMENT"                              , COMMENTSTART,
    "\\s"                                     , Token.SKIP,
    "#.*$"                                    , Token.SKIP,
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

