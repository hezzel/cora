/**************************************************************************************************
 Copyright 2024-2025 Cynthia Kop

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
import java.util.Set;
import charlie.util.Pair;
import charlie.parser.lib.Token;
import charlie.parser.lib.ParsingException;
import charlie.parser.lib.ParsingStatus;
import charlie.parser.Parser.ParserTerm;
import charlie.parser.Parser.Identifier;
import charlie.parser.CoraTokenData;
import charlie.parser.CoraParser;
import charlie.terms.*;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.rwinduction.engine.Equation;

/**
 * This class keeps track of a string and the progrss made while parsing through it.  This is
 * primarily designed to accommodate convenient parsing of Commands, and thus provides functionality
 * to parse single words, but also terms, equations and substitutions.
 */
public class CommandParsingStatus {
  private String _mystring;
  private int _index;
  private int _lastIndex;

  public CommandParsingStatus(String str) {
    _mystring = str;
    _index = 0;
    _lastIndex = -1;
    skipWhitespace();
  }

  /**
   * We make sure that _index always points at a non-whitespace character.
   */
  private void skipWhitespace() {
    while (_index < _mystring.length() && Character.isWhitespace(_mystring.charAt(_index))) {
      _index++;
    }
  }

  /**
   * Returns true if the whole string has been parsed: there are no further tokens left.
   */
  public boolean done() {
    return _index >= _mystring.length();
  }

  /**
   * Returns true if either the whole string has been parsed, or the next character is a
   * semi-colon.
   */
  public boolean commandEnded() {
    return _index >= _mystring.length() || _mystring.charAt(_index) == ';';
  }

  /**
   * If the next character is a semi-colon, this reads past it (and any subsequent whitespace) and
   * returns true.  If not, it simply returns false.
   */
  public boolean skipSeparator() {
    if (_index >= _mystring.length() || _mystring.charAt(_index) != ';') return false;
    _index++;
    skipWhitespace();
    return true;
  }

  /**
   * If the next character is not a semi-colon, and we are not yet at the end of the string, this
   * returns the upcoming text until the next whitespace or semi-colon, and then advances the
   * progress in the command parser beyond any following whitespace.
   *
   * If the next character is a semi-colon or we are at the end of a word, then null is returned
   * instead.  This is exactly the case if commandEnded() is true.
   */
  public String nextWord() {
    if (_index >= _mystring.length() || _mystring.charAt(_index) == ';') return null;
    _lastIndex = _index;
    for (_index += 1; _index < _mystring.length() && _mystring.charAt(_index) != ';' &&
                      !Character.isWhitespace(_mystring.charAt(_index)); _index++);
    String ret = _mystring.substring(_lastIndex, _index);
    skipWhitespace();
    return ret;
  }

  /**
   * This returns the remainder of the input, until either the end of the input string or the next
   * semi-colon.
   */
  public String readRest() {
    _lastIndex = _index;
    while (_index < _mystring.length() && _mystring.charAt(_index) != ';') _index++;
    return _mystring.substring(_lastIndex, _index);
  }

  /**
   * If the next part of _mystring is exactly text, this reads it and then skips any subsequent
   * whitespace, before returning true.
   * If not, then the next word is read, a failure message is printed, and false is returned.
   */
  public boolean expect(String text, Optional<OutputModule> module) {
    if (_index + text.length() <= _mystring.length() &&
        _mystring.substring(_index, _index + text.length()).equals(text)) {
      _lastIndex = _index;
      _index = _index + text.length();
      while (_index < _mystring.length() &&
             Character.isWhitespace(_mystring.charAt(_index))) _index++;
      return true;
    }
    if (commandEnded()) {
      module.ifPresent(o -> o.println("Unexpected end of input following token at position %a; " +
        "I expected %a.", previousPosition(), text));
      return false;
    }
    String word = nextWord();
    module.ifPresent(o -> o.println("Unexpected input at position %a; I expected %a but got %a.",
      previousPosition(), text, word));
    return false;
  }

  /**
   * This returns the current position in the initial string.  If the string has been fully read,
   * this will return the string's length instead.
   */
  public int currentPosition() {
    return _index + 1;
  }

  /** This returns the position in the initial string of the thing that was read. */
  public int previousPosition() {
    return _lastIndex + 1;
  }

  /**
   * Creates a ParsingStatus for the underlying word, advanced to the position where we're currently
   * reading.
   */
  private ParsingStatus makeStatus() {
    String alterString = " ".repeat(_index) + _mystring.substring(_index);
    return RIParser.createStatus(alterString);
  }

  /**
   * After reading from a ParsingStatus, this method updates _index to point to the next position
   * in the input.
   */
  private void recoverPosition(ParsingStatus status) {
    _lastIndex = _index;
    if (status.peekNext().isEof()) _index = _mystring.length();
    else _index = status.peekNext().getColumn() - 1;
  }

  /**
   * Given a ParsingException, this returns an appropriate error message to the given output module.
   */
  private void printErrorText(OutputModule module, ParsingException e) {
    String str = e.getMessage().trim();
    if (str.length() > 2 && str.substring(0,2).equals("1:") && Character.isDigit(str.charAt(2))) {
      module.println("Parsing error at position %a", str.substring(2));
    }
    else module.println("Parsing error: %a", str);
  }

  /**
   * This reads a single identifier into a string and returns it, or prints an error message to the
   * given OutputModule and returns null if the upcoming word is not an identifier.  In the latter
   * case, the current position is not advanced.
   */
  public String readIdentifier(Optional<OutputModule> module, String desc) {
    ParsingStatus status = makeStatus();
    try {
      Token tok = status.expect(CoraTokenData.IDENTIFIER, desc);
      String ret = tok.getText();
      recoverPosition(status);
      return ret;
    }
    catch (ParsingException e) {
      module.ifPresent(o -> printErrorText(o, e));
    }
    return null;
  }

  /**
   * This method reads a single function symbol from the underlying string from the current position
   * and returns the result, or prints an error message to the given OutputModule and returns null.
   * In the latter case, the parsing status may or may not be advanced, depending on the nature of
   * the problem.
   */
  public FunctionSymbol readSymbol(TRS trs, OutputModule module) {
    ParsingStatus status = makeStatus();
    Term fterm;
    try {
      ParserTerm pterm = CoraParser.readSingleSymbol(status);
      recoverPosition(status);
      fterm = CoraInputReader.readTerm(pterm, new Renaming(Set.of()), false, trs);
    }
    catch (ParsingException e) {
      printErrorText(module, e);
      return null;
    }
    if (!fterm.isConstant()) {
      module.println("Unexpected term %a at position %a; I expected a single constant.",
        _mystring.substring(_lastIndex, _index).trim(), _index);
      return null;
    }
    return fterm.queryRoot();
  }

  /**
   * This method reads a term from the underlying string at the current parsing position, and
   * returns the result.  If this fails, it instead prints an error message to the given
   * OutputModule and returns null.  Depending on the kind and position of the failure, the parsing
   * status may or may not be advanced.
   */
  public Term readTerm(TRS trs, Renaming varnames, OutputModule module) {
    ParsingStatus status = makeStatus();
    String vname = null;
    try {
      ParserTerm pterm = CoraParser.readTerm(status);
      if (pterm instanceof Identifier(Token tok, String name)) vname = name;
      recoverPosition(status);
      return CoraInputReader.readTerm(pterm, varnames, false, trs);
    }
    catch (ParsingException e) {
      if (vname != null) module.println("Unknown variable: " + vname);
      else printErrorText(module, e);
      return null;
    }
  }

  /**
   * This method reads an equation from the underlying string at the current parsing position, and
   * returns the result.  If this fails, it instead prints an error message to the given
   * OutputModule and returns null, and the status is not advanced.
   */
  public Pair<Equation,Renaming> readEquation(TRS trs, OutputModule module) {
    ParsingStatus status = makeStatus();
    try {
      Pair<Equation,Renaming> ret = EquationParser.parseEquation(status, trs);
      if (ret != null) recoverPosition(status);
      return ret;
    }
    catch (ParsingException e) {
      printErrorText(module, e);
      return null;
    }
  }

  /**
   * This method reads past a term in the input, not caring if the term type-checks but only if it
   * appears to be well-formed.
   */
  public boolean skipTerm() {
    ParsingStatus status = makeStatus();
    try {
      ParserTerm pterm = CoraParser.readTerm(status);
      recoverPosition(status);
      return true;
    }
    catch (ParsingException e) {
      return false;
    }
  }

  /**
   * This method reads a substitution from the underlying string at the current parsing position,
   * and returns the result.  If this fails, it instead prints an error message to the given
   * OutputModule and returns null.  Depending on the kind and position of the failure, the parsing
   * status may or may not be advanced.
   */
  public Substitution readSubstitution(TRS trs, Renaming keyNames, Renaming valueNames,
                                       OutputModule module) {
    // We make a ParsingStatus with *no* error tolerance.  This is important to avoice hanging.
    ParsingStatus status = makeStatus();
    Substitution ret = null;
    try { ret = parseSubstitution(status, trs, keyNames, valueNames, module); }
    catch (ParsingException e) { printErrorText(module, e); }

    if (ret == null) {
      // read past the ]
      while (!status.peekNext().isEof() &&
             !status.nextToken().getName().equals(CoraTokenData.METACLOSE));
    }
    recoverPosition(status);
    return ret;
  }

  /**
   * Helper function for readSubstitution: does the actual parsing using the CoraParser and
   * CoraInputReader.  Note that this function expects a ParsingStatus without any error
   * tolerance, since otherwise the function might hang indefinitely on some errors.
   * (But a ParsingStatus created by the RIParser has this property.)
   * In the case of success, a Substitution is returned; otherwise null.
   */
  private Substitution parseSubstitution(ParsingStatus status, TRS trs, Renaming keyNames,
                                         Renaming valueNames, OutputModule module) {
    status.expect(CoraTokenData.METAOPEN, "substitution opening bracket [");
    Substitution subst = TermFactory.createEmptySubstitution();
    boolean first = true;
    while (status.readNextIf(CoraTokenData.METACLOSE) == null) {
      if (first) first = false;
      else status.expect(CoraTokenData.COMMA, "comma");
      Token vartok = status.expect(CoraTokenData.IDENTIFIER, "(meta-)variable name");
      status.expect(RIParser.ASSIGN, ":=");
      ParserTerm pterm = CoraParser.readTerm(status);
      String varname = vartok.getText();
      Replaceable x = keyNames.getReplaceable(varname);
      if (x == null) { status.storeError(vartok, "No such variable: " + varname); return null; }
      Term term = CoraInputReader.readTerm(pterm, valueNames, true, trs);
      if (!x.queryType().equals(term.queryType())) {
        module.println("Ill-typed substitution: %a has type %a but is mapped to a term %a of " +
          "type %a.", varname, x.queryType(), term, term.queryType());
        return null;
      }
      subst.extend(x, term);
    }
    return subst;
  }
}

