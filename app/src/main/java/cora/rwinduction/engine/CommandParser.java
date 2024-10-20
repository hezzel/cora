package cora.rwinduction.engine;

import com.google.common.collect.ImmutableList;

import charlie.parser.lib.Token;
import charlie.parser.lib.ParsingStatus;
import charlie.parser.Parser;
import charlie.parser.CoraTokenData;
import charlie.parser.CoraParser;
import charlie.terms.Term;
import charlie.terms.Renaming;
import charlie.terms.TheoryFactory;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.rwinduction.engine.data.Equation;

class CommandParser {

  /**
   * This reads an equation of the form a = b | c from the given string
   * (and expects the string to end there).
   * If there is any error with the input, a ParseException will be thrown.
   * @throws charlie.exceptions.ParseException
   */
  public static Equation parseEquation(String str, TRS trs) {
    ParsingStatus status = new ParsingStatus(CoraTokenData.getConstrainedStringLexer(str), 1);
    Parser.ParserTerm ab = CoraParser.readTerm(status);
    Parser.ParserTerm a = null, b = null, c = null;
    if (!status.peekNext().isEof()) {
      status.expect(CoraTokenData.MID, "constraint bar: |");
      c = CoraParser.readTerm(status);
    }
    if (ab instanceof Parser.Application(Token tok1, Parser.ParserTerm head,
                                         ImmutableList<Parser.ParserTerm> args) &&
        head instanceof Parser.CalcSymbol(Token tok2, String name) &&
        args.size() == 2) {
      if (name.equals(CoraParser.EQUALS)) {
        a = args.get(0);
        b = args.get(1);
      }
    }
    if (a == null) {
      throw new charlie.exceptions.ParseException("Unexpected equation: " + str + "; I expected " +
        "a form \"a = b (| c)?\" but only found " + ab + ".");
    }
    Renaming renaming = new Renaming(trs.queryFunctionSymbolNames());
    Term l = CoraInputReader.readTerm(a, renaming, trs);
    Term r = CoraInputReader.readTerm(b, renaming, trs);
    Term constraint = c == null ? TheoryFactory.createValue(true)
                                : CoraInputReader.readTerm(c, renaming, trs);
    return new Equation(l, r, constraint, renaming);
  }

  static String[] split(String command) {

    return command.trim().split("\\s+");

  }

  static int parseIndex(String command) throws NumberFormatException {

    return Integer.parseInt(command);
  }

}
