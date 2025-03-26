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

package cora.rwinduction.parser;

import charlie.parser.lib.*;
import charlie.parser.Parser.*;
import charlie.parser.CoraTokenData;
import charlie.trs.TRS;

/**
 * This class defines the basics a parser for the input language of the interactive prover.
 * This includes the ability to parse equations, substitutions and commands.
 * Individual commands and sub-parsers should be implemented to handle individual commands.
 */
public class RIParser {
  public static final String APPROX = "APPROX";
  public static final String ASSIGN = "ASSIGN";
  public static final String SEPARATOR = "SEPARATOR";

  /**
   * This function checks if the given TRS is in principle allowed: there are no symbols in the
   * alphabet that would interfere with the extra symbols needed for the command parser language.
   *
   * If null is returned, everything is alright.  If a string is returned, it describes the error.
   */
  public static String checkTrs(TRS trs) {
    for (String s : trs.queryFunctionSymbolNames()) {
      if (s.indexOf("≈") >= 0 || s.indexOf(":=") >= 0 || s.indexOf(";") >= 0) {
        return "This TRS has a function symbol " + s + " that would interfere with the input " +
          "language of the interactive prover.  Therefore, it is unfortunately not possible to " +
          "use the interactive prover.";
      }
    }
    return null;
  }

  /**
   * We parse terms, equations and substitutions through an adaptation of the CoraInputReader.
   * To this end, we set up special tokens, and a parser that does not tolerate any errors.
   */
  public static ParsingStatus createStatus(String str) {
    String positionItem = "((-|!)?[0-9]+)";

    TokenQueue queue = CoraTokenData.getUpdatedConstrainedStringLexer(str,
        lexer -> new SplitApproxAndSeparatorLexer(lexer),
        "≈",    APPROX,
        "-><-", APPROX,
        ":=",   ASSIGN,
        ";",    SEPARATOR
      );
    return new ParsingStatus(queue, 1);
  }

  private static class SplitApproxAndSeparatorLexer extends TokenEditLexer {
    SplitApproxAndSeparatorLexer(Lexer lexer) { super(lexer, CoraTokenData.IDENTIFIER); }
    protected void modifyToken(Token token) throws LexerException {
      String txt = token.getText();
      int start = 0;
      while (start < txt.length()) {
        int best = txt.length();
        String bestKind = null;
        int a = txt.indexOf('≈', start);
        int b = txt.indexOf(';', start);
        if (a != -1) { best = a; bestKind = APPROX; }
        if (b != -1 && b < best) { best = b; bestKind = SEPARATOR; }
        if (best > start || bestKind == null) {
          String sub = txt.substring(start, best);
          Lexer sublexer = CoraTokenData.getConstrainedStringLexer(sub);
          while (true) {
            Token tok = sublexer.nextToken();
            if (tok.isEof()) break;
            storeToken(token, start + tok.getColumn() - 1, tok.getName(), tok.getText());
          }
        }
        if (bestKind != null) storeToken(token, best, bestKind, txt.substring(best, best+1));
        start = best + 1;
      }
    }
  }
}

