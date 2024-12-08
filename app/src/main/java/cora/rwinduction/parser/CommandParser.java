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

import com.google.common.collect.ImmutableList;

import charlie.util.FixedList;
import charlie.parser.lib.*;
import charlie.parser.Parser.*;
import charlie.parser.CoraTokenData;
import charlie.parser.CoraParser;
import charlie.terms.Term;
import charlie.terms.Renaming;
import charlie.terms.TheoryFactory;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.rwinduction.engine.Equation;

public class CommandParser {
  private static String APPROX = "APPROX";
  private static String ASSIGN = "ASSIGN";
  private static String SEPARATOR = "SEPARATOR";

  /**
   * This function checks if the given TRS is allowed: there are no symbols in the alphabet that
   * would interfere with the extra symbols needed for the command parser language.
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
  private static ParsingStatus createStatus(String str) {
    str = str.replace("≈", " ≈ ")
             .replace("-><-", " -><- ")
             .replace(":=", " := ")
             .replace(";", " ; ");
    TokenQueue queue = CoraTokenData.getUpdatedConstrainedStringLexer(str,
        "≈",    APPROX,
        "-><-", APPROX,
        ":=",   ASSIGN,
        ";",    SEPARATOR
      );
    return new ParsingStatus(queue, 1);
  }


  /**
   * This reads an equation of the form a ≈ b | c from the given string.
   * The string is expected to end after that.
   * If there is any error with the input, a ParseException will be thrown.
   * @throws charlie.exceptions.ParseException
   */
  public static Equation parseEquation(String str, TRS trs) {
    ParsingStatus status = createStatus(str);
    Equation ret = parseSingleEquation(status, trs);
    status.expect(Token.EOF, "end of input");
    return ret;
  }

  /**
   * This reads a non-empty list of equations of the form a ≈ b | c, separated by semi-colons,
   * from the given string.  The string is expected to end there.
   * If there is any error with the input, a ParseException will be thrown.
   * @throws charlie.exceptions.ParseException
   */
  public static FixedList<Equation> parseEquationList(String str, TRS trs) {
    ParsingStatus status = createStatus(str);
    FixedList.Builder<Equation> ret = new FixedList.Builder<Equation>();
    while (true) {
      ret.add(parseSingleEquation(status, trs));
      if (status.readNextIf(SEPARATOR) == null) {
        status.expect(Token.EOF, "semi-colon or end of input");
      }
      if (status.peekNext().isEof()) return ret.build();
    }
  }
  
  /** This reads an equation of the form a ≈ b | c from the given ParsingStatus */
  private static Equation parseSingleEquation(ParsingStatus status, TRS trs) {
    ParserTerm left, right = null, constr = null;
    left = CoraParser.readTerm(status);
    if (status.readNextIf(APPROX) != null) right = CoraParser.readTerm(status);
    else if (left instanceof Application(Token tok1, ParserTerm head,
                                         ImmutableList<ParserTerm> args) &&
             head instanceof CalcSymbol(Token tok2, String name) &&
             args.size() == 2 && name.equals(CoraParser.EQUALS)) {
      left = args.get(0);
      right = args.get(1);
    }
    if (right == null) {
      throw new charlie.exceptions.ParseException("Unexpected equation: I expected a form " +
        "\"a -><- b (| c)?\" but only found " + left + ".");
    }
    if (status.readNextIf(CoraTokenData.MID) != null) constr = CoraParser.readTerm(status);
    Renaming renaming = new Renaming(trs.queryFunctionSymbolNames());
    Term l = CoraInputReader.readTerm(left, renaming, trs);
    Term r = CoraInputReader.readTerm(right, renaming, trs);
    Term constraint = constr == null ? TheoryFactory.createValue(true)
                                     : CoraInputReader.readTerm(constr, renaming, trs);
    return new Equation(l, r, constraint, renaming);
  }
}

