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

package cora.parser;

import com.google.common.collect.ImmutableList;
import java.io.IOException;
import java.util.ArrayList;

import charlie.util.LookupMap;
import cora.types.*;
import cora.parser.lib.ErrorCollector;
import cora.parser.lib.Token;
import cora.parser.lib.ParsingStatus;
import cora.parser.InfixManager.OperatorData;

/**
 * This class reads text from string or file written in the .itrs format as used in the
 * termination problem database, Mixed_ITRS_2014.
 * This does not follow any formal definition (as I could not find this), but was derived from the
 * examples at:
 * https://github.com/TermCOMP/TPDB/tree/master/Integer_TRS_Innermost/Mixed_ITRS_2014
 */
public class ITrsParser extends FirstOrderParser implements Parser {
  public static String PLUS = "+";
  public static String MINUS = "-";
  public static String TIMES = "*";
  public static String DIV = "/";
  public static String MOD = "%";
  public static String GREATER = ">";
  public static String SMALLER = "<";
  public static String GEQ = "≥";
  public static String LEQ = "≤";
  public static String EQUALS = "=";
  public static String NEQ = "≠";
  public static String AND = "∧";
  public static String OR = "∨";
  public static String NOT = "not";

  private InfixManager _manager;

  /**
   * Stores the parsing status for use by methods of the ITrsParser class.
   * Private because it should only be called by the static methods that use an ITrsParser.
   */
  private ITrsParser(ParsingStatus status) {
    super(status, ITrsTokenData.IDENTIFIER, ITrsTokenData.BRACKETOPEN,
          ITrsTokenData.BRACKETCLOSE, ITrsTokenData.COMMA, ITrsTokenData.ARROW,
          ITrsTokenData.RULESDECSTART, ITrsTokenData.VARSDECSTART, ITrsTokenData.COMMENTSTART);
    _manager = new InfixManager();
    _manager.addGroup(InfixManager.ASSOC_LEFT, 1, AND);
    _manager.addGroup(InfixManager.ASSOC_LEFT, 1, OR);
    _manager.addGroup(InfixManager.ASSOC_NONE, 2, EQUALS, NEQ, GREATER, SMALLER, GEQ, LEQ);
    _manager.addGroup(InfixManager.ASSOC_LEFT, 3, PLUS, MINUS);
    _manager.addGroup(InfixManager.ASSOC_LEFT, 4, TIMES, DIV, MOD);
  }

  /**
   * Used for error recovery: returns if the given token is the start of a "section" in the trs or
   * mstr file.
   */
  protected boolean isSectionStart(Token token) {
    return token.getName().equals(ITrsTokenData.VARSDECSTART) ||
           token.getName().equals(ITrsTokenData.RULESDECSTART) ||
           token.getName().equals(ITrsTokenData.COMMENTSTART);
  }

  // ======================================== READING TERMS =======================================

  /**
   * term := mainterm
   *        | mainterm op term
   *
   * operator ::= PLUS | MINUS | TIMES | DIV | MOD | EQUAL | UNEQUAL | GREATER | SMALLER | GEQ |
   *              LEQ | AND | OR
   */
  protected ParserTerm readTerm() {
    ParserTerm ret = readMainTerm();
    if (ret == null) return null;

    OperatorData operator = tryReadOperator();
    if (operator == null) return ret;
    ArrayList<ParserTerm> parts = new ArrayList<ParserTerm>();
    ArrayList<OperatorData> ops = new ArrayList<OperatorData>();
    parts.add(ret);

    boolean errored = false;
    while (operator != null) {
      ops.add(operator);
      ParserTerm pt = readMainTerm();
      if (pt == null) { errored = true; ops.remove(ops.size()-1); break; }
      parts.add(pt);
      operator = tryReadOperator();
    }
    ret = _manager.convertChain(parts, ops, _status);
    if (errored) ret = new PErr(ret);
    return ret;
  }

  /**
   * mainterm ::= value
   *            | prefix
   *            | BRACKETOPEN term BRACKETCLOSE
   *            | firstorderterm
   *
   * where
   *   firstorderterm ::= IDENTIFIER
   *                    | IDENTIFIER BRACKETOPEN BRACKETCLOSE
   *                    | IDENTIFIER BRACKETOPEN term (COMMA term)* BRACKETCLOSE
   * (This is the same as for normal unsorted rewriting, and is handled by the inherit.)
   *
   * If an error is encountered, error recovery is done if possible (for example, missing brackets
   * may be filled in).  In this case, the term will be marked as containing Errors.
   */
  private  ParserTerm readMainTerm() {
    ParserTerm ret = tryReadValue();
    if (ret != null) return ret;
    ret = tryReadPrefix();
    if (ret != null) return ret;
    ret = tryReadBracketedTerm();
    if (ret != null) return ret;
    return readFirstOrderTerm();
  }

  /** value ::= TRUTH | FALSEHOOD | INTEGER */
  private ParserTerm tryReadValue() {
    // TRUTH
    Token token = _status.readNextIf(ITrsTokenData.TRUTH);
    if (token != null) return new BoolVal(token, true);
    // FALSEHOOD
    token = _status.readNextIf(ITrsTokenData.FALSEHOOD);
    if (token != null) return new BoolVal(token, false);
    // INTEGER
    token = _status.readNextIf(ITrsTokenData.INTEGER);
    if (token == null) return null;
    int x = 0;
    try { x = Integer.parseInt(token.getText()); }
    catch (NumberFormatException ex) {
      _status.storeError("Illegal integer: " + token.getText(), token);
    }
    return new IntVal(token, x);
  }

  /** prefix ::= (MINUS|NOT) mainterm */
  private ParserTerm tryReadPrefix() {
    ParserTerm head = null;
    Token token = _status.readNextIf(ITrsTokenData.MINUS);
    if (token != null) head = new CalcSymbol(token, MINUS);
    else {
      token = _status.readNextIf(ITrsTokenData.NOT);
      if (token != null) head = new CalcSymbol(token, NOT);
    }
    if (head == null) return null;
    ParserTerm ret = readMainTerm();
    if (ret == null) return null;
    return new Application(token, head, ImmutableList.of(ret));
  }

  /** bracketedterm ::= BRACKETOPEN term BRACKETCLOSE */
  private ParserTerm tryReadBracketedTerm() {
    Token token = _status.readNextIf(ITrsTokenData.BRACKETOPEN);
    if (token == null) return null;
    ParserTerm ret = readTerm();
    _status.expect(ITrsTokenData.BRACKETCLOSE, "closing bracket ')'");
    return ret;
  }

  private InfixManager.OperatorData tryReadOperator() {
    Token token = _status.readNextIf(ITrsTokenData.PLUS);
    if (token != null) return new OperatorData(token, PLUS);
    token = _status.readNextIf(ITrsTokenData.MINUS);
    if (token != null) return new OperatorData(token, MINUS);
    token = _status.readNextIf(ITrsTokenData.TIMES);
    if (token != null) return new OperatorData(token, TIMES);
    token = _status.readNextIf(ITrsTokenData.DIV);
    if (token != null) return new OperatorData(token, DIV);
    token = _status.readNextIf(ITrsTokenData.MOD);
    if (token != null) return new OperatorData(token, MOD);
    token = _status.readNextIf(ITrsTokenData.EQUAL);
    if (token != null) return new OperatorData(token, EQUALS);
    token = _status.readNextIf(ITrsTokenData.UNEQUAL);
    if (token != null) return new OperatorData(token, NEQ);
    token = _status.readNextIf(ITrsTokenData.GREATER);
    if (token != null) return new OperatorData(token, GREATER);
    token = _status.readNextIf(ITrsTokenData.SMALLER);
    if (token != null) return new OperatorData(token, SMALLER);
    token = _status.readNextIf(ITrsTokenData.GEQ);
    if (token != null) return new OperatorData(token, GEQ);
    token = _status.readNextIf(ITrsTokenData.LEQ);
    if (token != null) return new OperatorData(token, LEQ);
    token = _status.readNextIf(ITrsTokenData.AND);
    if (token != null) return new OperatorData(token, AND);
    token = _status.readNextIf(ITrsTokenData.OR);
    if (token != null) return new OperatorData(token, OR);
    return null;
  }

  // ====================================== READING FULL TRSs =====================================

  /**
   * rule ::= term ARROW term
   *        | term ARROW term MID term
   *
   * If this returns null, reading the rule failed, but at least one character (the arrow) has been
   * read, and error recovery may still be doable; with the right approach it might still be
   * possible to read the next rule.
   * Otherwise, it will either throw a ParseError or return an actual rule.  (If a rule is returned
   * it is not guaranteed that parsing was entirely successful, however; it is possible that some
   * errors have been stored in the status.)
   */
  protected ParserRule readRule(LookupMap<ParserDeclaration> vars) {
    ParserTerm left = readTerm();
    Token tok = _status.peekNext();
    if (_status.expect(ITrsTokenData.ARROW, "ARROW (->)") == null) _status.throwCollectedErrors();
    ParserTerm right = readTerm();
    ParserTerm constraint = null;
    if (_status.readNextIf(ITrsTokenData.MID) != null) constraint = readTerm();
    if (left == null || right == null) return null;
    return new ParserRule(tok, vars, left, right, constraint);
  }

  /**
   * trs ::= varlist? rules comment?
   */
  private ParserProgram readTRS() {
    LookupMap<ParserDeclaration> vars = readVarList();
    if (vars == null) vars = LookupMap.<ParserDeclaration>empty();
    ImmutableList<ParserRule> rules = readRules(vars);
    if (!readComment()) _status.expect(Token.EOF, "end of input");
    return new ParserProgram(LookupMap.<ParserDeclaration>empty(), rules);
  }

  // ====================================== PUBLIC FUNCTIONS ======================================

  /**
   * Helper function: creates a status to read the given string and store errors in the given
   * collector, which may be null (in which case errors are stored in a fresh collector in the
   * status).
   */
  private static ParsingStatus makeStatus(String str, ErrorCollector collector) {
    if (collector == null) collector = new ErrorCollector();
    return new ParsingStatus(ITrsTokenData.getStringLexer(str), collector);
  }

  /**
   * Helper function: checks that we have reached the end of input, and throws any collected
   * errors if throwErrors is true (and if there are errors in the status; if there aren't, the
   * function just returns).
   */
  private static void completeParsing(ParsingStatus status, boolean throwErrors) {
    status.expect(Token.EOF, "end of input");
    if (throwErrors) status.throwCollectedErrors();
  }

  /**
   * Reads a term from the given string.
   * @throws charlie.exceptions.ParseError
   */
  public static ParserTerm readTerm(String str, ErrorCollector collector) {
    ParsingStatus status = makeStatus(str, collector);
    ITrsParser parser = new ITrsParser(status);
    ParserTerm ret = parser.readTerm();
    completeParsing(status, collector == null || ret == null);
    return ret;
  }
  public static ParserTerm readTerm(String str) { return readTerm(str, null); }

  /**
   * Reads a rule from the given string.
   * @throws charlie.exceptions.ParseError
   */
  public static ParserRule readRule(String str, ErrorCollector collector) {
    ParsingStatus status = makeStatus(str, collector);
    ITrsParser parser = new ITrsParser(status);
    ParserRule rule = parser.readRule(LookupMap.<ParserDeclaration>empty());
    completeParsing(status, collector == null || rule == null);
    return rule;
  }
  public static ParserRule readRule(String str) { return readRule(str, null); }

  /**
   * Reads a set of variable declaration from the given string
   * @throws charlie.exceptions.ParseError
   */
  public static LookupMap<ParserDeclaration> readDeclarations(String str, ErrorCollector collect) {
    ParsingStatus status = makeStatus(str, collect);
    ITrsParser parser = new ITrsParser(status);
    LookupMap<ParserDeclaration> decl = parser.readVarList();
    completeParsing(status, collect == null || decl == null);
    return decl;
  }
  public static LookupMap<ParserDeclaration> readDeclarations(String str) {
    return readDeclarations(str, null);
  }

  /**
   * Reads a full TRS, in the expected format for the current parser, from the given string.
   */
  public static ParserProgram readProgramFromString(String str, ErrorCollector collector) {
    ParsingStatus status = makeStatus(str, collector);
    ITrsParser parser = new ITrsParser(status);
    ParserProgram program = parser.readTRS();
    if (collector == null || program == null) status.throwCollectedErrors();
    return program;
  }
  public static ParserProgram readProgramFromString(String str) {
    return readProgramFromString(str, null);
  }

  /**
   * Reads a full TRS, in the expected format for the current paser, from the given file.
   * @throws charlie.exceptions.ParseError
   */
  public static ParserProgram readProgramFromFile(String filename,
                                                  ErrorCollector collector) throws IOException {
    boolean dothrow = collector == null;
    if (collector == null) collector = new ErrorCollector();
    ParsingStatus status = new ParsingStatus(ITrsTokenData.getFileLexer(filename), collector);
    ITrsParser parser = new ITrsParser(status);
    ParserProgram program = parser.readTRS();
    if (dothrow || program == null) status.throwCollectedErrors();
    return program;
  }
  public static ParserProgram readProgramFromFile(String filename) throws IOException {
    return readProgramFromFile(filename, null);
  }
}

