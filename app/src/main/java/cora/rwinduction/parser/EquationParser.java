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
import charlie.util.Pair;
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
import cora.rwinduction.engine.EquationContext;

/**
 * The EquationParser uses the RIParser to parse (and read) Equations.
 */
public class EquationParser {
  /**
   * This reads an equation of the form a ≈ b | c from the given string.
   * The string is expected to end after that.
   * If there is any error with the input, a ParseException will be thrown.
   * @throws charlie.exceptions.ParseException
   */
  public static Pair<Equation,Renaming> parseEquation(String str, TRS trs) {
    ParsingStatus status = RIParser.createStatus(str);
    Pair<Equation,Renaming> ret = parseEquation(status, trs);
    status.expect(Token.EOF, "end of input");
    return ret;
  }

  /**
   * This reads an equation of the form a ≈ b | c from the given string, and returns the
   * EquationContext (•, a ≈ b | c, •), with the given index and an appropriate Renaming.
   * If there is any error with the input, a ParseException will be thrown.
   * @throws charlie.exceptions.ParseException
   */
  public static EquationContext parseEquationData(String str, TRS trs, int index) {
    ParsingStatus status = RIParser.createStatus(str);
    Pair<Equation,Renaming> pair = parseEquation(status, trs);
    EquationContext ret = new EquationContext(pair.fst(), index, pair.snd());
    status.expect(Token.EOF, "end of input");
    return ret;
  }

  /**
   * This reads a non-empty list of equations of the form a ≈ b | c, separated by semi-colons,
   * from the given string, and stores them as EquationContexts (•, a ≈ b | c, •).  The string
   * is expected to end after the list.
   * If there is any error with the input, a ParseException will be thrown.
   * The equations are assigned indexes 1..N, where N is the number of equations given.
   * @throws charlie.exceptions.ParseException
   */
  public static FixedList<EquationContext> parseEquationList(String str, TRS trs) {
    ParsingStatus status = RIParser.createStatus(str);
    FixedList.Builder<EquationContext> ret = new FixedList.Builder<EquationContext>();
    for (int index = 1; ; index++) {
      Pair<Equation,Renaming> pair = parseEquation(status, trs);
      ret.add(new EquationContext(pair.fst(), index, pair.snd()));
      if (status.readNextIf(RIParser.SEPARATOR) == null) {
        status.expect(Token.EOF, "semi-colon or end of input");
      }
      if (status.peekNext().isEof()) return ret.build();
    }
  }

  /**
   * This reads an Equation of the form a ≈ b | c from the given string, and returns both it and
   * the corresponding Renaming.  The ParsingStatus is advanced until after the equation.
   * If there is any error, a ParseException will be thrown.
   * @throws charlie.exceptions.ParseException
   */
  public static Pair<Equation,Renaming> parseEquation(ParsingStatus status, TRS trs) {
    ParserTerm left, right = null, constr = null;
    left = CoraParser.readTerm(status);
    if (status.readNextIf(RIParser.APPROX) != null) right = CoraParser.readTerm(status);
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
    checkEquation(l, r, constraint);
    return new Pair<Equation,Renaming>(new Equation(l, r, constraint), renaming);
  }

  /** This checks if the given equation is legal one, and throws a ParseException if not. */
  private static void checkEquation(Term left, Term right, Term constraint) {
    if (!left.queryType().equals(right.queryType())) {
      throw new ParseException("Left-hand side of equation (" + left.toString() + ") has type " + 
        right.queryType().toString() + " while right-hand side (" + right.toString() + ") has " +
        "type " + right.queryType().toString() + "!");
    }
    if (!constraint.queryType().equals(TypeFactory.boolSort)) {
      throw new ParseException("Constraint " + constraint.toString() + " has type " +
        constraint.toString() + " (should be Bool)");
    }
  }
}

