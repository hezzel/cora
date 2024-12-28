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

import charlie.exceptions.ParseException;
import charlie.util.FixedList;
import charlie.types.TypeFactory;
import charlie.parser.lib.*;
import charlie.parser.Parser.*;
import charlie.parser.CoraTokenData;
import charlie.parser.CoraParser;
import charlie.terms.*;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.rwinduction.engine.Equation;

public class ExtendedTermParser {
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

  /** This checks if the given Equation is a legal one, and throws a ParseException if not. */
  private static void checkEquation(Equation equation) {
    if (!equation.getLhs().queryType().equals(equation.getRhs().queryType())) {
      throw new ParseException("Left-hand side of equation " + equation + " has type " +
        equation.getLhs().queryType().toString() + " while right-hand side has type " +
        equation.getRhs().queryType().toString() + "!");
    }
    if (!equation.getConstraint().queryType().equals(TypeFactory.boolSort)) {
      throw new ParseException("Constraint of " + equation + " has type " +
        equation.getConstraint().toString() + " (should be Bool)");
    }
  }

  /**
   * This reads an equation of the form a ≈ b | c from the given string.
   * The string is expected to end after that.
   * If there is any error with the input, a ParseException will be thrown.
   * The equation is assigned the given index.
   * @throws charlie.exceptions.ParseException
   */
  public static Equation parseEquation(String str, TRS trs, int index) {
    ParsingStatus status = createStatus(str);
    Equation ret = parseSingleEquation(status, trs, index);
    checkEquation(ret);
    status.expect(Token.EOF, "end of input");
    return ret;
  }

  /**
   * This reads a non-empty list of equations of the form a ≈ b | c, separated by semi-colons,
   * from the given string.  The string is expected to end there.
   * If there is any error with the input, a ParseException will be thrown.
   * The equations are assigned indexes 1..N, where N is the number of equations given.
   * @throws charlie.exceptions.ParseException
   */
  public static FixedList<Equation> parseEquationList(String str, TRS trs) {
    ParsingStatus status = createStatus(str);
    FixedList.Builder<Equation> ret = new FixedList.Builder<Equation>();
    for (int index = 1; ; index++) {
      Equation eq = parseSingleEquation(status, trs, index);
      checkEquation(eq);
      ret.add(eq);
      if (status.readNextIf(SEPARATOR) == null) {
        status.expect(Token.EOF, "semi-colon or end of input");
      }
      if (status.peekNext().isEof()) return ret.build();
    }
  }
  
  /**
   * This reads an equation of the form a ≈ b | c from the given ParsingStatus, and assigns it the
   * given index.
   */
  private static Equation parseSingleEquation(ParsingStatus status, TRS trs, int index) {
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
    Term l = CoraInputReader.readTerm(left, renaming, true, trs);
    Term r = CoraInputReader.readTerm(right, renaming, true, trs);
    Term constraint = constr == null ? TheoryFactory.createValue(true)
                                     : CoraInputReader.readTerm(constr, renaming, true, trs);
    return new Equation(l, r, constraint, index, renaming);
  }

  /**
   * This reads a substitution of the form [x1:=term1,...,xn:=termn] from the given string, using
   * the first renaming to look up the keys, and the second renaming to look up the values.  The
   * latter Renaming may be modified, if some value includes fresh (meta-)variables.
   *
   * Note that this may absolutely throw a ParseException.
   */
  public static Substitution parseSubstitution(String str, TRS trs,
                                               Renaming keyNames, Renaming valueNames) {
    ParsingStatus status = createStatus(str);
    Substitution ret = TermFactory.createEmptySubstitution();
    status.expect(CoraTokenData.METAOPEN, "substitution opening bracket [");
    boolean first = true;
    while (status.readNextIf(CoraTokenData.METACLOSE) == null) {
      if (first) first = false;
      else status.expect(CoraTokenData.COMMA, "comma");
      Token vartok = status.expect(CoraTokenData.IDENTIFIER, "(meta-)variable name");
      status.expect(ASSIGN, ":=");
      ParserTerm pterm = CoraParser.readTerm(status);
      String varname = vartok.getText();
      Replaceable x = keyNames.getReplaceable(varname);
      if (x == null) { status.storeError("No such variable: " + varname, vartok); break; }
      Term term = CoraInputReader.readTerm(pterm, valueNames, true, trs);
      if (!x.queryType().equals(term.queryType())) {
        status.storeError(varname + " has type " + x.queryType().toString() + " but is mapped to " +
          "term " + term.toString() + " of type " + term.queryType().toString() + ".", vartok);
        break;
      }
      ret.extend(x, term);
    }
    status.expect(Token.EOF, "end of command");
    return ret;
  }
}

