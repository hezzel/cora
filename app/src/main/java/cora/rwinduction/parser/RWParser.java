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

import charlie.parser.lib.TokenQueue;
import charlie.parser.lib.ParsingStatus;
import charlie.parser.Parser.*;
import charlie.parser.CoraTokenData;
import charlie.trs.TRS;

/**
 * This class defines the basics a parser for the input language of the interactive prover.
 * This includes the ability to parse equations, substitutions and commands.
 * Individual commands and sub-parsers should be implemented to handle individual commands.
 */
public class RWParser {
  public static final String APPROX = "APPROX";
  public static final String ASSIGN = "ASSIGN";
  public static final String SEPARATOR = "SEPARATOR";
  public static final String EQPOS = "EQPOS";

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
    str = str.replace("≈", " ≈ ")
             .replace("-><-", " -><- ")
             .replace(":=", " := ")
             .replace(";", " ; ");

    String positionItem = "((-|!)?[0-9]+)";

    TokenQueue queue = CoraTokenData.getUpdatedConstrainedStringLexer(str,
        "≈",    APPROX,
        "-><-", APPROX,
        ":=",   ASSIGN,
        ";",    SEPARATOR,
        // We do not try to capture all equation positions as that might cause identifiers to be
        // misread: it is perfectly allowed to for instance have a function symbol L: instead, we
        // seek to parse those that are NOT valid identifiers; that is, those that contain a DOT.
        // Note that there is still some ambiguity remaining: technically, *1 or R*1 would also be
        // valid (partial) equation positions.  However, something like x*1 may well occur inside a
        // term, so we do not consider this in positions. (Users will just have to supply a .)
        "(L|R)?" +
        positionItem + "?" +
        "\\." +
        "(" + positionItem + "\\.)*" +
        "(" + positionItem + "|ε|e|☆[0-9]+|\\*[0-9]+)", EQPOS
      );
    return new ParsingStatus(queue, 1);
  }
}

