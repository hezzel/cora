/**************************************************************************************************
 Copyright 2024--2025 Cynthia Kop

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

import java.util.Optional;

import charlie.util.Pair;
import charlie.util.FixedList;
import charlie.types.TypeFactory;
import charlie.parser.lib.*;
import charlie.parser.Parser.*;
import charlie.parser.CoraTokenData;
import charlie.parser.CoraParser;
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.*;
import charlie.trs.TRS;
import charlie.printer.Printer;
import charlie.reader.CoraInputReader;
import cora.rwinduction.engine.Equation;
import cora.rwinduction.engine.EquationContext;

/**
 * The EquationParser uses the RIParser to parse (and read) Equations.
 */
public class EquationParser {
  /**
   * This reads an equation of the form a ≈ b | c from the given string.
   * The string is expected to end after that.
   * If there is any error with the input, a ParsingException will be thrown.
   * @throws charlie.parser.lib.ParsingException
   */
  public static Pair<Equation,MutableRenaming> parseEquation(String str, TRS trs) {
    ParsingStatus status = RIParser.createStatus(str);
    Pair<Equation,MutableRenaming> ret = parseEquation(status, trs);
    status.expect(Token.EOF, "end of input");
    return ret;
  }

  /**
   * This reads an equation context of the form (d, a ≈ b | c, e) from the given string.
   * The string is expected to end after that.
   * @throws charlie.parser.lib.ParsingException
   */
  public static EquationContext parseEquationContext(String str, int index, TRS trs) {
    ParsingStatus status = RIParser.createStatus(str);
    return parseEquationContext(status, index, trs);
  }

  /**
   * This reads an equation of the form a ≈ b | c from the given string, and returns the
   * EquationContext (•, a ≈ b | c, •), with the given index and an appropriate Renaming.
   * If there is any error with the input, a ParsingException will be thrown.
   * @throws charlie.parser.lib.ParsingException
   */
  public static EquationContext parseEquationData(String str, TRS trs, int index) {
    ParsingStatus status = RIParser.createStatus(str);
    Pair<Equation,MutableRenaming> pair = parseEquation(status, trs);
    EquationContext ret = new EquationContext(pair.fst(), index, pair.snd());
    status.expect(Token.EOF, "end of input");
    return ret;
  }

  /**
   * This reads a non-empty list of equations of the form a ≈ b | c, separated by semi-colons,
   * from the given string, and stores them as EquationContexts (•, a ≈ b | c, •).  The string
   * is expected to end after the list.
   * If there is any error with the input, a ParsingException will be thrown.
   * The equations are assigned indexes 1..N, where N is the number of equations given.
   * @throws charlie.parsing.lib.ParsingException
   */
  public static FixedList<EquationContext> parseEquationList(String str, TRS trs) {
    ParsingStatus status = RIParser.createStatus(str);
    FixedList.Builder<EquationContext> ret = new FixedList.Builder<EquationContext>();
    for (int index = 1; ; index++) {
      Pair<Equation,MutableRenaming> pair = parseEquation(status, trs);
      ret.add(new EquationContext(pair.fst(), index, pair.snd()));
      if (status.readNextIf(RIParser.SEPARATOR) == null) {
        status.expect(Token.EOF, "semi-colon or end of input");
      }
      if (status.peekNext().isEof()) return ret.build();
    }
  }

  /**
   * This reads an equation context of the form (d, a ≈ b | c, e) from the given string.
   * The ParsingStatus is advanced until after the equation.
   * If there is any error, an error will be stored in the status; hence, if the status is set up
   * not to store multiple errors, then a ParsingException will be thrown.
   * @throws charlie.parser.lib.ParsingException
   */
  public static EquationContext parseEquationContext(ParsingStatus status, int index, TRS trs) {
    if (status.expect(CoraTokenData.BRACKETOPEN, "opening bracket") == null) return null;
    ParserTerm leftgr = null, rightgr = null;
    Token tok = status.peekNext();
    if (tok.getText().equals("•") || tok.getText().equals("*")) status.nextToken();
    else leftgr = CoraParser.readTerm(status);
    status.expect(CoraTokenData.COMMA, "comma");
    Pair<Equation,MutableRenaming> pair = parseEquation(status, trs);
    status.expect(CoraTokenData.COMMA, "comma");
    tok = status.peekNext();
    if (tok.getText().equals("•") || tok.getText().equals("*")) status.nextToken();
    else rightgr = CoraParser.readTerm(status);
    status.expect(CoraTokenData.BRACKETCLOSE, "closing bracket");
    Optional<Term> lg, rg;
    if (leftgr == null) lg = Optional.empty();
    else lg = Optional.of(CoraInputReader.readTermAndUpdateNaming(leftgr, pair.snd(), trs));
    if (rightgr == null) rg = Optional.empty();
    else rg = Optional.of(CoraInputReader.readTermAndUpdateNaming(rightgr, pair.snd(), trs));
    return new EquationContext(lg, pair.fst(), rg, index, pair.snd());
  }

  /**
   * This reads an Equation of the form a ≈ b | c from the given string, and returns both it and
   * the corresponding Renaming.  The ParsingStatus is advanced until after the equation.
   * If there is any error, a ParsingException will be thrown.
   * @throws charlie.parser.lib.ParsingException
   */
  public static Pair<Equation,MutableRenaming> parseEquation(ParsingStatus status, TRS trs) {
    MutableRenaming renaming = new MutableRenaming(trs.queryFunctionSymbolNames());
    return new Pair<Equation,MutableRenaming>(parseEquation(status, renaming, trs), renaming);
  }

  /**
   * This reads an Equation of the form a ≈ b | c from the given string, using the given Renaming
   * for the variables (this Renaming may be expanded if additional variables occur in
   * equation).  The ParsingStatus is advanced until after the equation.
   * If there is any error, a ParsingException will be thrown (we assume that the ParsingStatus is
   * set up to tolerate 0 errors).
   * @throws charlie.parser.lib.ParsingException
   */
  public static Equation parseEquation(ParsingStatus status, MutableRenaming renaming, TRS trs) {
    Token tok = status.peekNext();
    ParserTerm left, right = null, constr = null;
    left = CoraParser.readTerm(status);
    if (status.readNextIf(RIParser.APPROX) != null) right = CoraParser.readTerm(status);
    else if (left instanceof Application(Token tok1, ParserTerm head,
                                         FixedList<ParserTerm> args) &&
             head instanceof CalcSymbol(Token tok2, String name) &&
             args.size() == 2 && name.equals(CoraParser.EQUALS)) {
      left = args.get(0);
      right = args.get(1);
    }
    Term l = CoraInputReader.readTermAndUpdateNaming(left, renaming, trs);
    if (right == null) {
      throw ParsingException.create(tok, "Unexpected equation: I expected a form " +
        "\"a -><- b (| c)?\" but only found one term: ",
        Printer.makePrintable(l, renaming), ".");
    }
    if (status.readNextIf(CoraTokenData.MID) != null) constr = CoraParser.readTerm(status);
    Term r = CoraInputReader.readTermAndUpdateNaming(right, renaming, trs);
    Term constraint = constr == null ? TheoryFactory.createValue(true)
                              : CoraInputReader.readTermAndUpdateNaming(constr, renaming, trs);
    checkEquation(tok, l, r, constraint, renaming);
    return new Equation(l, r, constraint);
  }

  /** This checks if the given equation is legal one, and throws a ParsingException if not. */
  private static void checkEquation(Token token, Term left, Term right, Term constraint,
                                    Renaming renaming) {
    if (!left.queryType().equals(right.queryType())) {
      throw ParsingException.create(token, "Left-hand side of equation (",
        Printer.makePrintable(left, renaming), ") has type ", left.queryType(),
        " while right-hand side (", Printer.makePrintable(right, renaming), ") has type ",
        right.queryType(), "!");
    }
    if (!constraint.queryType().equals(TypeFactory.boolSort)) {
      throw ParsingException.create(token, "Constraint ",
        Printer.makePrintable(constraint, renaming), " has type ", constraint.queryType(),
        " (should be Bool)");
    }
  }
}

