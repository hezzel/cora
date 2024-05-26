/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.parser;

import com.google.common.collect.ImmutableList;
import java.io.IOException;
import java.util.ArrayList;

import charlie.util.LookupMap;
import charlie.types.*;
import charlie.parser.lib.ErrorCollector;
import charlie.parser.lib.Token;
import charlie.parser.lib.ParsingStatus;

/**
 * This class reads text from string or file written in the .trs or .mstrs formats that up until
 * 2023 was used by the international confluence competition; this is a simplification of the old
 * human-readable format of the international termination competition.
 */
public class OCocoParser extends FirstOrderParser implements Parser {
  /**
   * Stores the parsing status for use by methods of the OCocoParser class.
   * Private because it should only be called by the static methods that use an OCocoParser.
   */
  private OCocoParser(ParsingStatus status) {
    super(status, OCocoTokenData.IDENTIFIER, OCocoTokenData.BRACKETOPEN,
          OCocoTokenData.BRACKETCLOSE, OCocoTokenData.COMMA, OCocoTokenData.ARROW,
          OCocoTokenData.RULESDECSTART, OCocoTokenData.VARSDECSTART, OCocoTokenData.COMMENTSTART);
  }

  /**
   * Used for error recovery: returns if the given token is the start of a "section" in the trs or
   * mstr file.
   */
  protected boolean isSectionStart(Token token) {
    return token.getName().equals(OCocoTokenData.VARSDECSTART) ||
           token.getName().equals(OCocoTokenData.SIGSTART) ||
           token.getName().equals(OCocoTokenData.RULESDECSTART) ||
           token.getName().equals(OCocoTokenData.COMMENTSTART);
  }

  // ======================================== READING TERMS =======================================

  /**
   * term ::= IDENTIFIER
   *        | IDENTIFIER BRACKETOPEN BRACKETCLOSE
   *        | IDENTIFIER BRACKETOPEN term (COMMA term)* BRACKETCLOSE
   *
   * If an error is encountered, error recovery is done if possible (for example, missing brackets
   * may be filled in).  In this case, the term will be marked as containing Errors.
   */
  protected  ParserTerm readTerm() {
    return readFirstOrderTerm();
  }

  // ================================ READING FUNCTION DECLARATIONS ===============================

  /**
   * type ::= IDENTIFIER* ARROW IDENTIFIER
   *
   * This function reads a sort declaration, and returns the corresponding type.
   * If the given input is not a sort declaration, then error recovery is done to construct a sort
   * declaration after all.  Hence, this cannot return null.
   */
  private Type readSortDeclaration() {
    Token next;
    ArrayList<Base> inputs = new ArrayList<Base>();
    while ((next = _status.readNextIf(OCocoTokenData.IDENTIFIER)) != null) {
      inputs.add(TypeFactory.createSort(next.getText()));
    }
    _status.expect(OCocoTokenData.ARROW, "IDENTIFIER (a sort) or the sort declaration arrow (->)");
    next = _status.expect(OCocoTokenData.IDENTIFIER, "output sort");
    Base output;
    if (next != null) output = TypeFactory.createSort(next.getText());
    else if (inputs.isEmpty()) output = TypeFactory.defaultSort;
    else {
      output = inputs.get(inputs.size()-1);
      inputs.remove(inputs.size()-1);
    }
    return TypeFactory.createSortDeclaration(inputs, output);
  }

  /**
   * Alternatively, an integer can be given in place of a type.  This function reads an integer
   * and returns the corresponding type.  If the given input is not an integer, then error recovery
   * is done and a Type is returned after all.
   */
  private Type readIntAsType() {
    Token token = _status.nextToken();
    String text = token.getText();
    try {
      int k = Integer.parseInt(text);
      if (k < 0) {
        _status.storeError("Cannot set arity below 0.", token);
        k = 0;
      }
      return TypeFactory.createDefaultArrow(k);
    }
    catch (NumberFormatException e) {
      _status.storeError("Unexpected identifier: " + text + ".  Expected an integer " +
        "(for the extended TRS format) or a sort declaration (for the MSTRS format).  Did you " +
        "forget ->?", token);
      return TypeFactory.createSort(text);
    }
  }

  /** 
   * fundec ::= BRACKETOPEN IDENTIFIER <integer> BRACKETCLOSE
   *          | BRACKETOPEN IDENTIFIER type BRACKETCLOSE
   *
   * If the given text is not a function declaration, then an attempt at error recovery is done,
   * and if this fails, a ParseException thrown.  If no error is thrown, then this function returns
   * a ParserDeclaration, not null.  It is guaranteed that calling this advances the parsing status
   * (or causes an error to be thrown).
   */
  private ParserDeclaration readFunctionDeclaration() {
    // BRACKETOPEN IDENTIFIER
    boolean endwithbracket = (_status.expect(OCocoTokenData.BRACKETOPEN,
                                             "an integer or sort declaration in brackets") != null);
    Token nametok = _status.expect(OCocoTokenData.IDENTIFIER, "a function name");
    if (nametok == null) _status.throwCollectedErrors();
    String name = nametok.getText();
    // make sure that we have the right kind of input to continue
    if (!_status.nextTokenIs(OCocoTokenData.IDENTIFIER) &&
        !_status.nextTokenIs(OCocoTokenData.ARROW)) {
      _status.abort("Unexpected token: expected either an integer (for the extended TRS " +
        "format), or a sort declaration (for the MSTRS format)", _status.peekNext());
    }

    Token next = _status.peekNext();
    Type type;
 
    // option 1: <integer>
    if (_status.nextTokensAre(new String[] { OCocoTokenData.IDENTIFIER,
                                             OCocoTokenData.BRACKETCLOSE })) {
      type = readIntAsType();
    }
    // option 2: type
    else {
      type = readSortDeclaration();
    }

    if (endwithbracket) _status.expect(OCocoTokenData.BRACKETCLOSE, "closing bracket");
    return new ParserDeclaration(nametok, name, type);
  }

  /** 
   * funlist ::= SIGSTART fundec* BRACKETCLOSE
   *
   * Function lists in UNSORTED TRSs have declarations of the form BRACKETOPEN IDENTIFIER <integer>
   * BRACKETCLOSE.  Function lists in MANY-SORTED TRSs have declarations of the form
   * BRACKETOPEN IDENTIFIER type BRACKETCLOSE.  Here, we handle both at once, and also allow
   * mixing up declarations.
   *
   * When presented with a function symbol list, this method reads the function symbols and returns
   * them.  Otherwise, nothing is read and null is returned.
   */
  private LookupMap<ParserDeclaration> readSignature() {
    Token start = _status.readNextIf(OCocoTokenData.SIGSTART);
    if (start == null) return null;

    LookupMap.Builder<ParserDeclaration> map = new LookupMap.Builder<ParserDeclaration>();
    
    while (true) {
      if (_status.readNextIf(OCocoTokenData.BRACKETCLOSE) != null) return map.build();
      if (_status.peekNext().isEof()) {
        _status.storeError("Unexpected end of input while reading (SIG.", _status.peekNext());
        return map.build();
      }
      if (isSectionStart(_status.peekNext())) {
        _status.storeError("Unexpected " + _status.peekNext().getText() + "; did you forget ) " +
          "to close (SIG?", _status.peekNext());
        return map.build();
      }
      ParserDeclaration decl = readFunctionDeclaration();
      if (map.containsKey(decl.name())) {
        _status.storeError("Redeclaration of function symbol " + decl.name() + ".", decl.token());
      }
      else map.put(decl.name(), decl);
    }
  }

  // ========================================= READING TRSs =======================================

  /**
   * rule ::= term ARROW term
   *
   * If this returns null, reading the rule failed, but at least one character (the arrow) has been
   * read, and error recovery may still be doable; with the right approach it might still be
   * possible to read the next rule.
   * Otherwise, it will either throw a ParseException or return an actual rule.  (If a rule is
   * returned it is not guaranteed that parsing was entirely successful, however; it is possible
   * that some errors have been stored in the status.)
   */
  protected ParserRule readRule(LookupMap<ParserDeclaration> vars) {
    ParserTerm left = readTerm();
    Token tok = _status.peekNext();
    if (_status.expect(OCocoTokenData.ARROW, "ARROW (->)") == null) _status.throwCollectedErrors();
    ParserTerm right = readTerm();
    if (left == null || right == null) return null;
    return new ParserRule(tok, vars, left, right);
  }

  /**
   * trs ::= varlist? funlist? rules comment?
   */
  private ParserProgram readTRS() {
    LookupMap<ParserDeclaration> vars = readVarList();
    if (vars == null) vars = LookupMap.<ParserDeclaration>empty();
    LookupMap<ParserDeclaration> funs = readSignature();
    if (funs == null) funs = LookupMap.<ParserDeclaration>empty();
    ImmutableList<ParserRule> rules = readRules(vars);
    if (!readComment()) _status.expect(Token.EOF, "end of input");
    return new ParserProgram(funs, rules);
  }

  // ====================================== PUBLIC FUNCTIONS ======================================

  /**
   * Helper function: creates a status to read the given string and store errors in the given
   * collector, which may be null (in which case errors are stored in a fresh collector in the
   * status).
   */
  private static ParsingStatus makeStatus(String str, ErrorCollector collector) {
    if (collector == null) collector = new ErrorCollector();
    return new ParsingStatus(OCocoTokenData.getStringLexer(str), collector);
  }

  /**
   * Reads a term from the given string.
   * @throws charlie.exceptions.ParseException
   */
  public static ParserTerm readTerm(String str, ErrorCollector collector) {
    ParsingStatus status = makeStatus(str, collector);
    OCocoParser parser = new OCocoParser(status);
    ParserTerm ret = parser.readTerm();
    status.expect(Token.EOF, "end of input");
    if (collector == null || ret == null) status.throwCollectedErrors();
    return ret;
  }
  public static ParserTerm readTerm(String str) { return readTerm(str, null); }

  /**
   * Reads a rule from the given string.
   * @throws charlie.exceptions.ParseException
   */
  public static ParserRule readRule(String str, ErrorCollector collector) {
    ParsingStatus status = makeStatus(str, collector);
    OCocoParser parser = new OCocoParser(status);
    ParserRule rule = parser.readRule(LookupMap.<ParserDeclaration>empty());
    status.expect(Token.EOF, "end of input");
    if (collector == null || rule == null) status.throwCollectedErrors();
    return rule;
  }
  public static ParserRule readRule(String str) { return readRule(str, null); }

  /**
   * Reads either the signature, or a set of variable declaration from the given string
   * @throws charlie.exceptions.ParseException
   */
  public static LookupMap<ParserDeclaration> readDeclarations(String str, ErrorCollector collect) {
    ParsingStatus status = makeStatus(str, collect);
    OCocoParser parser = new OCocoParser(status);
    LookupMap<ParserDeclaration> decl = parser.readSignature();
    if (decl == null) decl = parser.readVarList();
    status.expect(Token.EOF, "end of input");
    if (collect == null || decl == null) status.throwCollectedErrors();
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
    OCocoParser parser = new OCocoParser(status);
    ParserProgram program = parser.readTRS();
    if (collector == null || program == null) status.throwCollectedErrors();
    return program;
  }
  public static ParserProgram readProgramFromString(String str) {
    return readProgramFromString(str, null);
  }

  /**
   * Reads a full TRS, in the expected format for the current paser, from the given file.
   * @throws charlie.exceptions.ParseException
   */
  public static ParserProgram readProgramFromFile(String filename,
                                                  ErrorCollector collector) throws IOException {
    boolean dothrow = collector == null;
    if (collector == null) collector = new ErrorCollector();
    ParsingStatus status = new ParsingStatus(OCocoTokenData.getFileLexer(filename), collector);
    OCocoParser parser = new OCocoParser(status);
    ParserProgram program = parser.readTRS();
    if (dothrow || program == null) status.throwCollectedErrors();
    return program;
  }
  public static ParserProgram readProgramFromFile(String filename) throws IOException {
    return readProgramFromFile(filename, null);
  }
}

