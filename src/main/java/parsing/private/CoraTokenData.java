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
import java.util.ArrayList;
import java.util.Collections;
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
  public static String DECLARE        = "DECLARE";
  public static String LAMBDA         = "LAMBDA";
  public static String DOT            = "DOT";
  public static String ARROW          = "ARROW";
  public static String RULEARROW      = "RULEARROW";
  public static String TYPEARROW      = "TYPEARROW";
  // The following are only used for constrained TRSs. */
  public static String INTEGER        = "INTEGER";
  public static String TRUE           = "TRUE";
  public static String FALSE          = "FALSE";
  public static String STRING         = "STRING";
  public static String PLUS           = "PLUS";
  public static String MINUS          = "MINUS";
  public static String TIMES          = "TIMES";
  public static String DIV            = "DIV";
  public static String GEQ            = "GEQ";
  public static String GREATER        = "GREATER";
  public static String LEQ            = "LEQ";
  public static String SMALLER        = "SMALLER";
  public static String AND            = "AND";
  public static String OR             = "OR";
  public static String NOT            = "NOT";
  public static String IMPLIES        = "IMPLIES";
  public static String INTTYPE        = "INTTYPE";
  public static String BOOLTYPE       = "BOOLTYPE";
  public static String STRINGTYPE     = "STRINGTYPE";
  public static String COLON          = "COLON";

  /** Unconstrained TRSs admit a more broad range of identifiers. */
  private static String[] utokens = new String[] {
    "([^\\s()\\[\\]⟨⟩\\{\\}\"',:λ\\.\\*\\\\\\.→⇒/-]|(-(?!>))|(/(?!\\*))|(\\*(?!/)))+" , IDENTIFIER,
      // identifiers are built from any characters other than whitespace, brackets (of any kind),
      // braces, quotes, commas, colons, lambda, backslash, dot, or unicode arrows
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
    "/"                                       , DIV,
    ">"                                       , GREATER,
    "<"                                       , SMALLER,
    "≥|(>=)"                                  , GEQ,
    "≤|(<=)"                                  , LEQ,
    "∧|(/\\\\)"                               , AND,
    "∨|(\\\\/)"                               , OR,
    "(not)|¬"                                 , NOT,
    "=>"                                      , IMPLIES,
    "Int"                                     , INTTYPE,
    "Bool"                                    , BOOLTYPE,
    "String"                                  , STRINGTYPE,
    "([^\\s()\\[\\]⟨⟩\\{\\}\"',:λ\\.\\*\\+\\\\\\.><=≥≤→⇒∧∨¬/-]|)+" , IDENTIFIER,
      // identifiers are now built from any characters other than whitespace, brackets (of any
      // kind), braces, quotes, colons, lambda, dot, *, -, +, >, =, <, ≥, ≤, /, \, ¬
      // unicode arrows
  };

  /** Both constrained and unconstrained TRSs share the tokens below. */
  private static String[] shared = new String[] {
    "\"([^\"\\\\]|(\\\\.))*$"                 , "PARTIALSTRING",
    "\"([^\"\\\\]|(\\\\.))*\\\\$"             , "PARTIALSTRING",
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
    "\\s"                                     , Token.SKIP,
  };

  private static String[] unconstrainedTokens = null;
  private static String[] constrainedTokens = null;

  private static String[] getUnconstrainedTokens() {
    if (unconstrainedTokens == null) {
      ArrayList<String> tmp = new ArrayList<String>();
      Collections.addAll(tmp, utokens);
      Collections.addAll(tmp, shared);
      unconstrainedTokens = tmp.toArray(new String[tmp.size()]);
    }
    return unconstrainedTokens;
  }

  private static String[] getConstrainedTokens() {
    if (constrainedTokens == null) {
      ArrayList<String> tmp = new ArrayList<String>();
      Collections.addAll(tmp, ctokens);
      Collections.addAll(tmp, shared);
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

