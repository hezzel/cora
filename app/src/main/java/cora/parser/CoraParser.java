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

import cora.types.*;
import cora.utils.LookupMap;
import cora.parser.lib.*;
import cora.parser.InfixManager.OperatorData;

/**
 * The CoraParser parses the main Cora input format -- both for the unconstrained basic formalisms
 * (which do not have any theory symbols), and the constrained ones (which currently include all
 * the standard formalisms).
 */
public class CoraParser implements Parser {
  public static final String PLUS = "+";
  public static final String MINUS = "-";
  public static final String TIMES = "*";
  public static final String DIV = "/";
  public static final String MOD = "%";
  public static final String GREATER = ">";
  public static final String SMALLER = "<";
  public static final String GEQ = "≥";
  public static final String LEQ = "≤";
  public static final String EQUALS = "=";
  public static final String NEQ = "≠";
  public static final String AND = "∧";
  public static final String OR = "∨";
  public static final String NOT = "¬";

  /**
   * The parser keeps track of the status of parser so far; all read functions have a (potential)
   * side effect of advancing the parsing status.
   */
  private ParsingStatus _status;

  /** This infix manager is used for parsing (sub-)terms with infix operators. */
  private InfixManager _manager;

  /**
   * Stores the parsing status for use by methods of the CoraParser class.
   * Private because the CoraParser should only be created by the static methods in the class.
   */
  private CoraParser(ParsingStatus status) {
    _status = status;
    _manager = new InfixManager();
    _manager.addGroup(InfixManager.ASSOC_LEFT, 1, AND);
    _manager.addGroup(InfixManager.ASSOC_LEFT, 1, OR);
    _manager.addGroup(InfixManager.ASSOC_NONE, 2, EQUALS, NEQ, GREATER, SMALLER, GEQ, LEQ);
    _manager.addGroup(InfixManager.ASSOC_LEFT, 3, PLUS, MINUS);
    _manager.addGroup(InfixManager.ASSOC_LEFT, 4, TIMES, DIV, MOD);
  }

  // ===================================== PARSING CONSTANTS ======================================

  /**
   * This function checks if the next tokens represent a string, and if so, returns the string.
   * If not, null is returned and nothing is read.
   */
  private String tryReadIdentifier() {
    Token next = _status.readNextIf(CoraTokenData.IDENTIFIER);
    if (next != null) return next.getText();
    return null;
  }

  // ======================================== READING TYPES =======================================

  /**
   * type ::= nonarrowtype (typearrow type)?
   *
   * This function reads a type and returns it.
   * The input is expected to actually be a type. If this is not the case, then an error is stored.
   * If some kind of error recovery could be done, a Type is still returned; otherwise, null may be
   * returned, even if something was read -- indicating that we will have to do large-scale error
   * recovery.
   */
  private Type readType() {
    Type start = readNonArrowType();
    if (_status.readNextIf(CoraTokenData.ARROW) == null) return start;
    Type end = readType();
    if (start != null && end != null) return TypeFactory.createArrow(start, end);
    // error recovery
    if (start == null) return end;
    return start;
  }

  /**
   * nonarrowtype ::= basictype_1 TIMES...TIMES basictype_n with n ≥ 1
   *
   * This function reads a non-arrow type and returns it.  The input is expected to actually start
   * with a non-arrow type.  If this is not the case, then an error is stored and either null is
   * returned, or whatever Type we did manage to read.
   */
  private Type readNonArrowType() {
    Type start = readBasicType();
    if (!tryReadTimes()) return start;
    ImmutableList.Builder<Type> builder = ImmutableList.<Type>builder();
    if (start != null) builder.add(start);
    do {
      Type next = readBasicType();
      if (next != null) builder.add(next);
    } while (tryReadTimes());
    return TypeFactory.createProduct(builder.build());
  }

  /**
   * basictype ::= sort
   *             | BRACKETOPEN type BRACKETCLOSE
   *
   * where
   * sort ::= INTTYPE | BOOLTYPE | STRINGTYPE | IDENTIFIER
   */
  private Type readBasicType() {
    if (_status.readNextIf(CoraTokenData.INTTYPE) != null) return TypeFactory.intSort;
    if (_status.readNextIf(CoraTokenData.BOOLTYPE) != null) return TypeFactory.boolSort;
    if (_status.readNextIf(CoraTokenData.STRINGTYPE) != null) return TypeFactory.stringSort;
    String name = tryReadIdentifier();
    if (name != null) return TypeFactory.createSort(name);
    Token bracket = _status.expect(CoraTokenData.BRACKETOPEN,
      "a type (started by a sort identifier or bracket)");
    if (bracket == null) return null;
    Type ret = readType();
    _status.expect(CoraTokenData.BRACKETCLOSE, "closing bracket");
    return ret;
  }

  /**
   * Product types may be indicated using * or × separators.  While × is the special PRODUCT token,
   * the symbol * is also used for multiplication in constrained formalisms.  Hence, in constrained
   * systems this is NOT marked as the PRODUCT symbol, but when it occurs in the context of a type
   * it clearly indicates a product separator.
   * This method checks if the next token is * or × and if so, reads it and returns true; if not,
   * nothing is read and false is returned.
   */
  private boolean tryReadTimes() {
    if (_status.readNextIf(CoraTokenData.PRODUCT) != null) return true;
    if (_status.readNextIf(CoraTokenData.TIMES) != null) return true;
    return false;
  }

  // ======================================== READING TERMS =======================================

  /**
   * term = abstraction
   *      | mainterm (infixsymbol mainterm)*
   *
   * When the current parsing status represents a term, this method reads it into a ParserTerm.
   * This function expects to read a term; if it fails, error recovery is attempted to still return
   * a term, but if that fails altogether, null is returned.  It is possible, but not guaranteed,
   * that symbols were still read if null is returned.
   */
  private  ParserTerm readTerm() {
    if (_status.nextTokenIs(CoraTokenData.LAMBDA)) return readAbstraction();
    ParserTerm ret = readMainTerm();
    if (ret == null) return null;

    OperatorData operator = tryReadInfixSymbol();
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
      operator = tryReadInfixSymbol();
    }   
    ret = _manager.convertChain(parts, ops, _status);
    if (errored) ret = new PErr(ret);
    return ret;
  }

  /**
   * mainterm = value
   *          | IDENTIFIER
   *          | IDENTIFIER METAOPEN termlist METACLOSE
   *          | mainterm BRACKETOPEN termlist BRACKETCLOSE
   *          | BRACKETOPEN term BRACKETCLOSE
   *          | TUPLEOPEN termlist TUPLECLOSE
   *          | METAOPEN infixsymbol METACLOSE
   *          | NOT mainterm
   *          | MINUS mainterm
   */
  private ParserTerm readMainTerm() {
    ParserTerm ret = null;
    Token token;

    // NOT mainterm
    if ((token =_status.readNextIf(CoraTokenData.NOT)) != null) {
      ParserTerm child = readMainTerm();
      if (child == null) return new CalcSymbol(token, NOT);
      return new Application(token, new CalcSymbol(token, NOT), ImmutableList.of(child));
    }

    // MINUS mainterm
    if ((token = _status.readNextIf(CoraTokenData.MINUS)) != null) {
      ParserTerm child = readMainTerm();
      if (child == null) return new CalcSymbol(token, MINUS);
      if (child instanceof IntVal(Token t, int v)) return new IntVal(token, -v);
      return new Application(token, new CalcSymbol(token, MINUS), ImmutableList.of(child));
    }

    // value
    if (_status.nextTokenIs(CoraTokenData.STRING) ||
        _status.nextTokenIs(CoraTokenData.INTEGER) ||
        _status.nextTokenIs(CoraTokenData.TRUE) ||
        _status.nextTokenIs(CoraTokenData.FALSE)) {
      ret = readValue();
    }

    // BRACKETOPEN term BRACKETCLOSE  -- we store term as ret
    else if (_status.readNextIf(CoraTokenData.BRACKETOPEN) != null) {
      ret = readTerm();
      if (ret == null) { _status.readNextIf(CoraTokenData.BRACKETCLOSE); return null; }
      if (_status.expect(CoraTokenData.BRACKETCLOSE, "a closing bracket") == null) {
        return new PErr(ret);
      }
    }

    // METAOPEN infixsymbol METACLOSE
    else if (_status.readNextIf(CoraTokenData.METAOPEN) != null) {
      token = _status.peekNext();
      OperatorData data = tryReadInfixSymbol();
      if (data == null && _status.readNextIf(CoraTokenData.NOT) != null) {
        data = new OperatorData(token, NOT);
      }
      if (data == null) {
        _status.storeError("Expected infix symbol but got " + token.getName() + " (" +
          token.getText() + ")", token);
        ret = new PErr(new Identifier(token, token.getText()));
        _status.nextToken();
      }
      else {
        ret = new CalcSymbol(data.token(), data.name());
      }
      Token end = _status.expect(CoraTokenData.METACLOSE, "infix closing bracket ]");
      if (end == null) return new PErr(ret);
    }

    // TUPLEOPEN termlist TUPLECLOSE
    else if ((token = _status.readNextIf(CoraTokenData.TUPLEOPEN)) != null) {
      ImmutableList<ParserTerm> args =
        readTermList(CoraTokenData.TUPLECLOSE, "tuple closing bracket ⦈");
      if (args == null || args.size() == 0) {
        ret = new PErr(new Identifier(token, "⦇⦈"));
        if (args != null) _status.storeError("Empty tuples are not allowed.", token);
      }
      else if (args.size() == 1) {
        _status.storeError("Tuples of length 1 are not allowed.", token);
        ret = args.get(0);
      }
      else ret = new Tup(token, args);
    }

    // IDENTIFIER
    else {
      token = _status.expect(CoraTokenData.IDENTIFIER, "term, started by an identifier, " +
        "λ, string or (,");
      if (token == null) return null;
      Token next;
      // IDENTIFIER METAOPEN termlist METACLOSE
      if ((next = _status.readNextIf(CoraTokenData.METAOPEN)) != null) {
        ImmutableList args = readTermList(CoraTokenData.METACLOSE, "meta-closing bracket " +
          (next.getText().equals("[") ? "]" : "⟩"));
        if (args == null) ret = new PErr(new Meta(token, token.getText(), ImmutableList.of()));
        else ret = new Meta(token, token.getText(), args);
      }
      // just IDENTIFIER (so a function symbol or variable)
      else ret = new Identifier(token, token.getText());
    }

    // if we see an argument list, read it, and make the application structure
    while (_status.readNextIf(CoraTokenData.BRACKETOPEN) != null) {
      ImmutableList args = readTermList(CoraTokenData.BRACKETCLOSE, "closing bracket )");
      if (args == null) ret = new PErr(ret);
      else ret = new Application(ret.token(), ret, args);
    }

    return ret;
  }

  /**
   * abstraction ::= LAMBDA vardec (COMMA vardec)* DOT term
   *
   * where
   * vardec ::= IDENTIFIER
   *          | IDENTIFIER DECLARE type
   */
  private ParserTerm readAbstraction() {
    // read λ
    if (_status.expect(CoraTokenData.LAMBDA, "a λ") == null) return null;
    boolean errored = false;

    // read every (name,type) combination into (variables,type); when type is not given, this
    // component is simply left null
    ArrayList<Token> tokens = new ArrayList<Token>();
    ArrayList<String> variables = new ArrayList<String>();
    ArrayList<Type> types = new ArrayList<Type>();
    while (true) {
      String name = null;
      Type type = null;

      Token token = _status.expect(CoraTokenData.IDENTIFIER, "an identifier (variable name)");
      if (token != null) name = token.getText();
      if (_status.readNextIf(CoraTokenData.DECLARE) != null) {
        type = readType();
        if (type == null) errored = true;
      }

      if (name != null) {
        tokens.add(token);
        variables.add(name);
        types.add(type);
      }
      else errored = true;

      // stop reading once we encounter a .
      if (_status.readNextIf(CoraTokenData.DOT) != null) break;
      // following an identifier and a type, the only alternative is a comma; if this is not
      // supplied, we either continue reading anyway (after giving an error), or abort if there are
      // no more variable names to come
      if (_status.expect(CoraTokenData.COMMA, "a comma or dot") == null) {
        if (!_status.nextTokenIs(CoraTokenData.IDENTIFIER)) { errored = true; break; }
      }
    }
    // we read LAMBDA vardec (COMMA vardec)* DOT, so now just read the term (which extends as far
    // as it can)
    ParserTerm ret = readTerm();
    if (ret == null) return null;

    // put everything together
    for (int i = variables.size()-1; i >= 0; i--) {
      ret = new Lambda(tokens.get(i), variables.get(i), types.get(i), ret);
    }
    if (errored) ret = new PErr(ret);
    return ret;
  }

  /**
   * value = STRING+ | INT | TRUE | FALSE
   *
   * This function is really only called when we already know the next token is a string, int, or
   * boolean constant, so should not fail.  In the case of strings, it eagerly reads as many
   * strings as are available.
   */
  private ParserTerm readValue() {
    Token token = _status.nextToken();
    if (token.getName().equals(CoraTokenData.TRUE)) return new BoolVal(token, true);
    if (token.getName().equals(CoraTokenData.FALSE)) return new BoolVal(token, false);
    if (token.getName().equals(CoraTokenData.INTEGER)) {
      try {
        int number = Integer.parseInt(token.getText());
        return new IntVal(token, number);
      }
      catch (NumberFormatException e) {
        _status.storeError("Cannot parse integer constant: " + token.getText(), token);
        return new Identifier(token, token.getText());
      }
    }
    if (!token.getName().equals(CoraTokenData.STRING)) {
      throw new Error("Calling readValueStructure when it shouldn't be.");
    }
    // take the token's text without the closing "
    StringBuilder text =
      new StringBuilder(token.getText().substring(0, token.getText().length()-1));
    Token next;
    while ( (next = _status.readNextIf(CoraTokenData.STRING)) != null) {
      // for each subsequent string, append it without quotes
      text.append(next.getText().substring(1, next.getText().length()-1));
    }
    // append a final quote to make sure the string is well-formed
    text.append("\"");
    return new StringVal(token, text.toString());
  }

  /**
   * termlist ::= ε [followName] | term (COMMA term)* [followName]
   *
   * The terms are returned as an ImmutableList.
   */
  private ImmutableList<ParserTerm> readTermList(String followName, String followDescription) {
    // handle the case ε [followName]
    if (_status.readNextIf(followName) != null) return ImmutableList.of();

    Token token;
    ArrayList<ParserTerm> ret = new ArrayList<ParserTerm>();
    boolean errored = false;    // keep track of if we should mark the next term as an error

    // read the arguments until we encounter [followName] or we're in an overly weird place
    while (true) {
      // appropriate error handling if we see commas where there shouldn't be
      if ((token = _status.readNextIf(CoraTokenData.COMMA)) != null) {
        _status.storeError("Unexpected comma; expected term or " + followDescription, token);
        errored = true;
        while (_status.readNextIf(CoraTokenData.COMMA) != null);
      }
      // read the next term in the list
      ParserTerm arg = readTerm();
      if (arg == null) errored = true;
      else {
        if (errored) { arg = new PErr(arg); errored = false; }
        ret.add(arg);
      }
      if (_status.readNextIf(followName) != null) break;
      if (_status.expect(CoraTokenData.COMMA, "a comma or " + followDescription) == null) {
        // we recover from a missing comma, but only if we're still followed by another term
        errored = true;
        if (!nextMayBeTerm()) break;
      }
    }
    if (errored) {
      if (ret.size() == 0) return null;
      ret.set(ret.size()-1, new PErr(ret.get(ret.size()-1)));
    }
    return ImmutableList.copyOf(ret);
  }

  /**
   * If the next token is an infix operator, this function reads it and returns the corresponding
   * OperatorData.  If not, nothing is read and null is returned.
   */
  private OperatorData tryReadInfixSymbol() {
    Token token = _status.peekNext();
    if (_status.readNextIf(CoraTokenData.PLUS) != null)    return new OperatorData(token, PLUS);
    if (_status.readNextIf(CoraTokenData.MINUS) != null)   return new OperatorData(token, MINUS);
    if (_status.readNextIf(CoraTokenData.TIMES) != null)   return new OperatorData(token, TIMES);
    if (_status.readNextIf(CoraTokenData.DIV) != null)     return new OperatorData(token, DIV);
    if (_status.readNextIf(CoraTokenData.MOD) != null)     return new OperatorData(token, MOD);
    if (_status.readNextIf(CoraTokenData.AND) != null)     return new OperatorData(token, AND);
    if (_status.readNextIf(CoraTokenData.OR) != null)      return new OperatorData(token, OR);
    if (_status.readNextIf(CoraTokenData.GREATER) != null) return new OperatorData(token, GREATER);
    if (_status.readNextIf(CoraTokenData.SMALLER) != null) return new OperatorData(token, SMALLER);
    if (_status.readNextIf(CoraTokenData.GEQ) != null)     return new OperatorData(token, GEQ);
    if (_status.readNextIf(CoraTokenData.LEQ) != null)     return new OperatorData(token, LEQ);
    if (_status.readNextIf(CoraTokenData.EQUAL) != null)   return new OperatorData(token, EQUALS);
    if (_status.readNextIf(CoraTokenData.UNEQUAL) != null) return new OperatorData(token, NEQ);
    return null;
  }

  /**
   * Returns true if it should be possible to read at least one token towards a term structure in
   * the current status.
   */
  private boolean nextMayBeTerm() {
    return _status.nextTokenIs(CoraTokenData.LAMBDA) ||
           _status.nextTokenIs(CoraTokenData.STRING) ||
           _status.nextTokenIs(CoraTokenData.INTEGER) ||
           _status.nextTokenIs(CoraTokenData.TRUE) ||
           _status.nextTokenIs(CoraTokenData.FALSE) ||
           _status.nextTokenIs(CoraTokenData.BRACKETOPEN) ||
           _status.nextTokenIs(CoraTokenData.METAOPEN) ||
           _status.nextTokenIs(CoraTokenData.IDENTIFIER);
  }

  // ======================================== READING RULES =======================================

  private ParserRule readRule(LookupMap<ParserDeclaration> vars) {
    return null;
    // TODO
  }
  
  private ImmutableList<ParserRule> readRules() {
    ImmutableList.Builder<ParserRule> ret = ImmutableList.<ParserRule>builder();
    // TODO
    return ret.build();
  }

  // ====================================== READING FULL TRSs =====================================

  private LookupMap<ParserDeclaration> readDeclarations() {
    return null;
    // TODO
  }

  private ParserProgram readTRS() {
    return null;
    // TODO
  }

  // ====================================== PUBLIC FUNCTIONS ======================================

  /**
   * Helper function: creates a status to read the given string and store errors in the given
   * collector, which may be null (in which case errors are stored in a fresh collector in the
   * status).
   */
  private static ParsingStatus makeStatus(String str, boolean constrained,
                                          ErrorCollector collector) {
    if (collector == null) collector = new ErrorCollector();
    TokenQueue queue;
    if (constrained) queue = CoraTokenData.getConstrainedStringLexer(str);
    else queue = CoraTokenData.getUnconstrainedStringLexer(str);
    return new ParsingStatus(queue, collector);
  }

  /** Helper function to make sure we are done parsing, and have no errors */
  private static void finish(ParsingStatus status, boolean throwErrors) {
    status.expect(Token.EOF, "end of input");
    if (throwErrors) status.throwCollectedErrors();
  }

  /**  
   * Reads the given type from string.
   * If constrainedTRS is set to true, then Int, Bool and String are recognised as pre-defined
   * sorts, and identifiers are restricted as they are when reading a constrained TRS (e.g., sort
   * names may not contain "+").  If it is set to false, then identifiers are more general and
   * the pre-defined types will not be marked as theory sorts.
   * @throws cora.exceptions.ParseError
   */
  public static Type readType(String str, boolean constrainedTRS, ErrorCollector collector) {
    ParsingStatus status = makeStatus(str, constrainedTRS, collector);
    CoraParser parser = new CoraParser(status);
    Type ret = parser.readType();
    finish(status, collector == null || ret == null);
    return ret; 
  }

  /**
   * Reads the given type from string, recognising the pre-defined sorts.
   * This is the same as readTypeFromString(true, null).
   */
   public static Type readType(String str) { return readType(str, true, null); }

  /**
   * Reads a term from the given string.
   * If constrainedTRS is set to true, then tokens for theories and constraints are recognised and
   * parsed accordingly; if not, these are just identifiers.
   * The error collector is allowed to be null.  If an error collector is given, then parsing tries
   * error recovery, and stores its erorrs in the given collector; only if parsing really fails is
   * an error thrown.  If the given collector is null, any error causes a ParseError to be thrown
   * (although we still try to collect all relevant errors in the same ParseError).
   * @throws cora.exceptions.ParseError
   */
  public static ParserTerm readTerm(String str, boolean constrainedTRS, ErrorCollector collector) {
    ParsingStatus status = makeStatus(str, constrainedTRS, collector);
    CoraParser parser = new CoraParser(status);
    ParserTerm ret = parser.readTerm();
    finish(status, collector == null || ret == null);
    return ret;
  }

  /**
   * Reads a rule from the given string.
   * @throws cora.exceptions.ParseError
   */
  public static ParserRule readRule(String str, boolean constrained, ErrorCollector collector) {
    ParsingStatus status = makeStatus(str, constrained, collector);
    CoraParser parser = new CoraParser(status);
    ParserRule rule = parser.readRule(LookupMap.<ParserDeclaration>empty());
    finish(status, collector == null || rule == null);
    return rule;
  }
  public static ParserRule readRule(String str) { return readRule(str, true, null); }

  /**
   * Reads zero or more function or variable declarations from the given string.
   * @throws cora.exceptions.ParseError
   */
  public static LookupMap<ParserDeclaration> readDeclarations(String str, boolean constrained,
                                                              ErrorCollector collector) {
    ParsingStatus status = makeStatus(str, constrained, collector);
    CoraParser parser = new CoraParser(status);
    LookupMap<ParserDeclaration> decl = parser.readDeclarations();
    finish(status, collector == null || decl == null);
    return decl;
  }
  public static LookupMap<ParserDeclaration> readDeclarations(String str) {
    return readDeclarations(str, true, null);
  }

  /**
   * Reads a full TRS from the given string, allowing theory symbols and constraints if and only
   * if constrained is set to true.
   */
  public static ParserProgram readProgramFromString(String str, boolean constrained,
                                                    ErrorCollector collector) {
    ParsingStatus status = makeStatus(str, constrained, collector);
    CoraParser parser = new CoraParser(status);
    ParserProgram program = parser.readTRS();
    finish(status, collector == null || program == null);
    return program;
  }
  public static ParserProgram readProgramFromString(String str) {
    return readProgramFromString(str, true, null);
  }

  /**
   * Reads a full TRS, in the expected format for the current paser, from the given file.
   * @throws cora.exceptions.ParseError
   */
  public static ParserProgram readProgramFromFile(String filename, boolean constrained,
                                                  ErrorCollector collector) throws IOException {
    TokenQueue queue;
    if (constrained) queue = CoraTokenData.getConstrainedFileLexer(filename);
    else queue = CoraTokenData.getUnconstrainedFileLexer(filename);
    ParsingStatus status =
      new ParsingStatus(queue, collector == null ? new ErrorCollector() : collector);
    CoraParser parser = new CoraParser(status);
    ParserProgram program = parser.readTRS();
    finish(status, collector == null || program == null);
    return program;
  }
}

