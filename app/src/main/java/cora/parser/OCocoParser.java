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
import cora.parser.lib.ErrorCollector;
import cora.parser.lib.Token;
import cora.parser.lib.ParsingStatus;

/**
 * This class reads text from string or file written in the .trs or .mstrs formats that up until
 * 2023 was used by the international confluence competition; this is a simplification of the old
 * human-readable format of the international termination competition.
 */
public class OCocoParser implements Parser {
  /**
   * The parser keeps track of the status of parser so far; all read functions have a (potential)
   * side effect of advancing the parsing status.
   */
  private final ParsingStatus _status;

  /**
   * Stores the parsing status for use by methods of the OCocoParser class.
   * Private because it should only be called by the static methods that use an OCocoParser.
   */
  private OCocoParser(ParsingStatus status) {
    _status = status;
  }

  /**
   * Used for error recovery: returns if the given token is the start of a "section" in the trs or
   * mstr file.
   */
  private boolean isSectionStart(Token token) {
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
  private  ParserTerm readTerm() {
    // first we should have an IDENTIFIER
    Token start = _status.expect(OCocoTokenData.IDENTIFIER,
                                 "an identifier (variable or function name)");
    if (start == null) return null;
    ParserTerm head = new Identifier(start, start.getText());
    // if we don't follow up with a BRACKETOPEN, then that's enough
    if (_status.readNextIf(OCocoTokenData.BRACKETOPEN) == null) return head;
    // if we follow the BRACKETOPEN with a BRACKETCLOSE, then that's enough
    if (_status.readNextIf(OCocoTokenData.BRACKETCLOSE) != null) {
      return new Application(start, head, ImmutableList.of());
    }
    // otherwise, start reading recursively
    ImmutableList.Builder<ParserTerm> builder = ImmutableList.<ParserTerm>builder();
    ArrayList<ParserTerm> args = new ArrayList<ParserTerm>();
    boolean errored = false;
    while (true) {
      ParserTerm child = readTerm();
      if (child == null) errored = true;
      else builder.add(child);
      // if we encounter BRACKETCLOSE, we have finished this term
      if (_status.readNextIf(OCocoTokenData.BRACKETCLOSE) != null) break;
      // otherwise we must encounter COMMA followed by at least one more term
      if (_status.expect(OCocoTokenData.COMMA, "a comma or closing bracket") == null) {
        // error situation: if they may have just forgotten a comma, pretend we saw one and
        // continue, but otherwise return what we already have
        errored = true;
        if (!_status.nextTokenIs(OCocoTokenData.IDENTIFIER)) break;
      }
    }
    ParserTerm ret = new Application(start, head, builder.build());
    if (errored) return new PErr(ret);
    else return ret;
  }

  // ======================================== READING RULES =======================================

  /**
   * rule ::= term ARROW term
   *
   * If this returns null, reading the rule failed, but at least one character (the arrow) has been
   * read, and error recovery may still be doable; with the right approach it might still be
   * possible to read the next rule.
   * Otherwise, it will either throw a ParseError or return an actual rule.  (If a rule is returned
   * it is not guaranteed that parsing was entirely successful, however; it is possible that some
   * errors have been stored in the status.)
   */
  private ParserRule readRule(LookupMap<ParserDeclaration> vars) {
    ParserTerm left = readTerm();
    Token tok = _status.peekNext();
    if (_status.expect(OCocoTokenData.ARROW, "ARROW (->)") == null) _status.throwCollectedErrors();
    ParserTerm right = readTerm();
    if (left == null || right == null) return null;
    return new BasicRule(tok, vars, left, right);
  }

  /**
   * rules ::= RULESDECSTART rule* BRACKETCLOSE
   *
   * The current status is expected to start with RULESDECSTART (if not, we store an error and
   * return the empty list).  We read and return the rules, or throw a ParseError if the rules list
   * is poorly shaped.
   *
   * If any variables have already been declared, these are passed in the argument list, to be
   * stored as part of the rule.  (This map is allowed to be empty, but not null.)
   */
  private ImmutableList<ParserRule> readRules(LookupMap<ParserDeclaration> declaredVars) {
    ImmutableList.Builder<ParserRule> ret = ImmutableList.<ParserRule>builder();
    if (_status.expect(OCocoTokenData.RULESDECSTART, "rules declaration") == null) {
      return ret.build();
    }
    while (_status.readNextIf(OCocoTokenData.BRACKETCLOSE) == null) {
      ParserRule r = readRule(declaredVars);
      if (r != null) ret.add(r);
    }
    return ret.build();
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
    else if (inputs.isEmpty()) output = TypeFactory.unitSort;
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
      return TypeFactory.createUnitArrow(k);
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
   * and if this fails, a ParseError thrown.  If no error is thrown, then this function returns a
   * ParserDeclaration, not null.  It is guaranteed that calling this advances the parsing status
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

  // ====================================== READING FULL TRSs =====================================

  /**
   * varlist ::= VARSDECSTART IDENTIFIER* BRACKETCLOSE
   *
   * When presented with a varlist, this function saves all the variables into the returned
   * mapping, with the unit sort as their type (since varlists can only occur in UNSORTED TRSs).
   * When presented with anything else, it returns null (and does not read anything).
   */
  private LookupMap<ParserDeclaration> readVarList() {
    Token start = _status.readNextIf(OCocoTokenData.VARSDECSTART);
    if (start == null) return null;
    LookupMap.Builder<ParserDeclaration> ret = new LookupMap.Builder<ParserDeclaration>();
    while (true) {
      Token next = _status.nextToken();
      if (next.getName().equals(OCocoTokenData.BRACKETCLOSE)) return ret.build();
      if (next.getName().equals(OCocoTokenData.IDENTIFIER)) {
        String name = next.getText();
        if (ret.containsKey(name)) {
          _status.storeError("Double declaration of variable " + name, next);
        }
        else ret.put(name, new ParserDeclaration(next, name, TypeFactory.unitSort));
      }
      else {
        // error handling for incorrect tokens
        if (next.isEof()) {
          _status.storeError("Encountered end of input while reading varlist; no closing bracket " +
                             "given.", start);
          return ret.build();
        }
        if (isSectionStart(next)) {
          _status.storeError("Unexpected " + next.getText() + " while reading varlist; did you " +
            "forget a closing bracket?", next);
          _status.pushBack(next);
          return ret.build();
        }
        // if we encounter something else, it's unclear what the programmer did, so let's just
        // abort the parsing process
        _status.abort("Unexpected token: " + next.getText() + " (" + next.getName() +
          "); expected a variable name", next);
      }
    }
  }

  /**
   * comment ::= COMMENTOPEN string BRACKETCLOSE EOF
   * If the current status starts with COMMENTOPEN, we read until the end of the file and store an
   * error if the last bracket is not right before it; in this case we return true.
   * If it starts with something else, we return false and read nothing.
   */
  private boolean readComment() {
    Token start = _status.readNextIf(OCocoTokenData.COMMENTSTART);
    if (start == null) return false;
    Token token = _status.nextToken();
    Token lastFollow = null;
    while (!token.isEof()) {
      if (token.getName().equals(OCocoTokenData.BRACKETCLOSE)) {
        lastFollow = _status.nextToken();
        if (lastFollow.isEof()) return true;
      }
      token = _status.nextToken();
    }
    if (lastFollow == null) _status.storeError("Unclosed comment.", start);
    else _status.storeError("Unexpected token: " + lastFollow.getText() + "; expected end of " +
      "input following comment.", lastFollow);
    return true;
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
   * @throws cora.exceptions.ParseError
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
   * @throws cora.exceptions.ParseError
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
   * @throws cora.exceptions.ParseError
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
   * @throws cora.exceptions.ParseError
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

