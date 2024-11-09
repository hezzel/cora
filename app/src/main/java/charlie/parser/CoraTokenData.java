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
import java.util.ArrayList;
import java.util.Collections;
import charlie.parser.lib.*;

/**
 * This file defines the tokens used to lex and parse a file or string using Cora's internal
 * input format.  It is used by the CoraParser and intentionally not public.
 */
class CoraTokenData {
  /* First we define constants for all the tokens. */
  public static final String IDENTIFIER     = "IDENTIFIER";
  public static final String BRACKETOPEN    = "BRACKETOPEN";
  public static final String BRACKETCLOSE   = "BRACKETCLOSE";
  public static final String BRACEOPEN      = "BRACEOPEN";
  public static final String BRACECLOSE     = "BRACECLOSE";
  public static final String METAOPEN       = "METAOPEN";
  public static final String METACLOSE      = "METACLOSE";
  public static final String TUPLEOPEN      = "TUPLEOPEN";
  public static final String TUPLECLOSE     = "TUPLECLOSE";
  public static final String COMMA          = "COMMA";
  public static final String DECLARE        = "DECLARE";
  public static final String LAMBDA         = "LAMBDA";
  public static final String DOT            = "DOT";
  public static final String ARROW          = "ARROW";
  public static final String PUBLIC         = "PUBLIC";
  public static final String PRIVATE        = "PRIVATE";
  // The following are only used for constrained TRSs. */
  public static final String INTEGER        = "INTEGER";
  public static final String TRUE           = "TRUE";
  public static final String FALSE          = "FALSE";
  public static final String STRING         = "STRING";
  public static final String PLUS           = "PLUS";
  public static final String MINUS          = "MINUS";
  public static final String TIMES          = "TIMES";
  public static final String MID            = "MID";
  public static final String DIV            = "DIV";
  public static final String MOD            = "MOD";
  public static final String GEQ            = "GEQ";
  public static final String GREATER        = "GREATER";
  public static final String LEQ            = "LEQ";
  public static final String SMALLER        = "SMALLER";
  public static final String EQUAL          = "EQUAL";
  public static final String EQUALINT       = "EQUALINT";
  public static final String EQUALSTRING    = "EQUALSTRING";
  public static final String UNEQUAL        = "UNEQUAL";
  public static final String UNEQUALINT     = "UNEQUALINT";
  public static final String UNEQUALSTRING  = "UNEQUALSTRING";
  public static final String AND            = "AND";
  public static final String OR             = "OR";
  public static final String NOT            = "NOT";
  public static final String IMPLIES        = "IMPLIES";
  public static final String INTTYPE        = "INTTYPE";
  public static final String BOOLTYPE       = "BOOLTYPE";
  public static final String STRINGTYPE     = "STRINGTYPE";
  public static final String COLON          = "COLON";

  /** Unconstrained TRSs admit a more broad range of identifiers. */
  private static String[] utokens = new String[] {
    "([^\\s()\\[\\]⟨⟩\\{\\}⦇⦈\"',:λ×\\.\\*\\\\\\.→/-]|(:(?!:))|(-(?!>))|(/(?!\\*))|(\\*(?!/)))+" , IDENTIFIER,
      // identifiers are built from any characters other than whitespace, brackets (of any kind),
      // braces, quotes, commas, colons, lambda, backslash, dot, × or unicode arrows
      // they also may not contain -> or /* or */
    "\"([^\"\\\\]|(\\\\.))*\""                , "ILLEGALSTRING",
  };

  /** Constrained TRSs have special cases for the in-built symbols. */
  private static String[] ctokens = new String[] {
    "0|([1-9][0-9]*)"                         , INTEGER,
    "0[0-9]+"                                 , "BADINT",
    "true"                                    , TRUE,
    "false"                                   , FALSE,
    "\"([^\"\\\\]|(\\\\.))*\""                , STRING,
    "\\+"                                     , PLUS,
    "-"                                       , MINUS,
    "\\*"                                     , TIMES,
    "\\|"                                     , MID,
    ":"                                       , COLON,
    "/"                                       , DIV,
    "%"                                       , MOD,
    ">"                                       , GREATER,
    "<"                                       , SMALLER,
    "≥|(>=)"                                  , GEQ,
    "≤|(<=)"                                  , LEQ,
    "="                                       , EQUAL,
    "=_Int"                                   , EQUALINT,
    "=_String"                                , EQUALSTRING,
    "≠"                                       , UNEQUAL,
    "≠_Int"                                   , UNEQUALINT,
    "≠_String"                                , UNEQUALSTRING,
    "!="                                      , UNEQUAL,
    "!=_Int"                                  , UNEQUALINT,
    "!=_String"                               , UNEQUALSTRING,
    "∧|(/\\\\)"                               , AND,
    "∨|(\\\\/)"                               , OR,
    "(not)|¬"                                 , NOT,
    "=>"                                      , IMPLIES,
    "Int"                                     , INTTYPE,
    "Bool"                                    , BOOLTYPE,
    "String"                                  , STRINGTYPE,
    "([^\\s()\\[\\]⟨⟩\\{\\}⦇⦈\"',:λ%\\.\\|\\*\\+\\\\\\.><=!≠≥≤→∧∨¬/-]|)+" , IDENTIFIER,
      // identifiers are now built from any characters other than whitespace, brackets (of any
      // kind), braces, quotes, colons, lambda, dot, mid, or the operators / relation symbols
      // *, %, -, +, >, =, !, ≠, <, ≥, ≤, /, \, ¬, →
  };

  /** Both constrained and unconstrained TRSs share the tokens below. */
  private static String[] shared = new String[] {
    "\"([^\"\\\\]|(\\\\.))*$"                 , "PARTIALSTRING",
    "\"([^\"\\\\]|(\\\\.))*\\\\$"             , "PARTIALSTRING",
    "\\("                                     , BRACKETOPEN,
    "\\)"                                     , BRACKETCLOSE,
    "⦇"                                       , TUPLEOPEN,
    "⦈"                                       , TUPLECLOSE,
    "\\(\\|"                                  , TUPLEOPEN,
    "\\|\\)"                                  , TUPLECLOSE,
    "\\{"                                     , BRACEOPEN,
    "\\}"                                     , BRACECLOSE,
    "⟨"                                       , METAOPEN,
    "⟩"                                       , METACLOSE,
    "\\["                                     , METAOPEN,
    "\\]"                                     , METACLOSE,
    ","                                       , COMMA,
    "::"                                      , DECLARE,
    "λ"                                       , LAMBDA,
    "\\\\"                                    , LAMBDA,
    "\\."                                     , DOT,
    "->"                                      , ARROW,
    "→"                                       , ARROW,
    "private"                                 , PRIVATE,
    "public"                                  , PUBLIC,
    "/\\*"                                    , "COMMENTOPEN",
    "\\*/"                                    , "COMMENTCLOSE",
    "\\s"                                     , Token.SKIP,
  };

  private static String[] unconstrainedTokens = null;
  private static String[] constrainedTokens = null;

  private static String[] getUnconstrainedTokens() {
    if (unconstrainedTokens == null) {
      ArrayList<String> tmp = new ArrayList<String>();
      Collections.addAll(tmp, shared);
      Collections.addAll(tmp, utokens);
      unconstrainedTokens = tmp.toArray(new String[tmp.size()]);
    }
    return unconstrainedTokens;
  }

  private static String[] getConstrainedTokens() {
    if (constrainedTokens == null) {
      ArrayList<String> tmp = new ArrayList<String>();
      Collections.addAll(tmp, shared);
      Collections.addAll(tmp, ctokens);
      constrainedTokens = tmp.toArray(new String[tmp.size()]);
    }
    return constrainedTokens;
  }

  private static TokenQueue setupLexer(Lexer base, boolean constrained) {
    Lexer lexer = base;
    lexer = LexerFactory.createNestedCommentRemoverLexer(lexer, "COMMENTOPEN", "COMMENTCLOSE");
    if (constrained) lexer = new BadIntWarner(lexer);
    else lexer = new IllegalStringWarner(lexer);
    lexer = new PartialStringWarner(lexer);
    return LexerFactory.createPushbackLexer(lexer);
  }

  /** Returns a TokenQueue that goes through the given file, tokenising for an unconstrained TRS. */
  public static TokenQueue getUnconstrainedFileLexer(String filename) throws IOException {
    return setupLexer(LexerFactory.createFileLexer(getUnconstrainedTokens(), filename), false);
  }

  /** Returns a TokenQueue that goes through the given file, tokenising for a constrained TRS. */
  public static TokenQueue getConstrainedFileLexer(String filename) throws IOException {
    return setupLexer(LexerFactory.createFileLexer(getConstrainedTokens(), filename), true);
  }

  /** Returns a TokenQueue that goes through a string, tokenising for an unconstrained TRS. */
  public static TokenQueue getUnconstrainedStringLexer(String text) {
    return setupLexer(LexerFactory.createStringLexer(getUnconstrainedTokens(), text), false);
  }

  /** Returns a TokenQueue that goes through the given string, tokenising for a constrained TRS. */
  public static TokenQueue getConstrainedStringLexer(String text) {
    return setupLexer(LexerFactory.createStringLexer(getConstrainedTokens(), text), true);
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

  /**
   * Helper class used to throw an error when encountering a string constant even though we are
   * using the unconstrained lexer which does not support strings.
   */
  private static class IllegalStringWarner extends TokenEditLexer {
    IllegalStringWarner(Lexer lexer) { super(lexer, "ILLEGALSTRING"); }
    protected void modifyToken(Token token) throws LexerException {
      storeToken(token, 0, STRING, token.getText());
      throw new LexerException(token, "String constants are only allowed in constrained systems.");
    }
  }

  /**
   * Helper class used to throw an error when encountering integers whose first digit is a 0, but
   * afterwards process them as proper int constants.
   */
  private static class BadIntWarner extends TokenEditLexer {
    BadIntWarner(Lexer lexer) { super(lexer, "BADINT"); }
    protected void modifyToken(Token token) throws LexerException {
      String txt = token.getText();
      int i = 0;
      while (i < txt.length() && txt.charAt(i) == '0') i++;
      if (i < txt.length()) txt = txt.substring(i);
      else txt = "0";
      storeToken(token, 0, INTEGER, txt);
      throw new LexerException(token, "Illegal integer constant: " + token.getText() + ".");
    }
  }
}

