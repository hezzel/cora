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

package cora.parsing;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Set;
import java.util.TreeMap;
import cora.exceptions.IllegalRuleError;
import cora.exceptions.ParseError;
import cora.parsing.lib.Token;
import cora.parsing.lib.ParsingStatus;
import cora.types.*;
import cora.terms.*;
import cora.rewriting.*;

/**
 * This class reads text from string or file written in the .trs or .mstrs formats from the
 * international confluence competition.
 */
public class TrsInputReader {
  private static class TermStructure {
    Token root;
    ArrayList<TermStructure> children;
    boolean errored;
    TermStructure(Token t) {
      root = t;
      errored = false;
      children = new ArrayList<TermStructure>();
    }
  }

  /**
   * The reader keeps track of the status of reading so far; all read functions have a (potential)
   * side effect of advancing the parsing status.
   */
  private ParsingStatus _status;
  /**
   * The reader keeps track of the declared variables, and the function symbols encountered so far.
   */
  private SymbolData _symbols;

  /**
   * Stores the parsing status for use by methods of the TrsInputReader class.
   * Private because it should only be called by the static methods that use a TrsInputReader.
   */
  private TrsInputReader(ParsingStatus status) {
    _status = status;
    _symbols = new SymbolData();
  }

  /**
   * Stores the parsing status for use by methods of the TrsInputReader class, and stores the
   * given TRS into the SymbolData used to parse terms.
   * Private because it should only be called by the static methods that use a TrsInputReader.
   */
  private TrsInputReader(ParsingStatus status, TRS trs) {
    _status = status;
    _symbols = new SymbolData(trs);
  }

  /**
   * Used for error recovery: returns if the given token is the start of a "section" in the trs or
   * mstr file.
   */
  private boolean isSectionStart(Token token) {
    return token.getName().equals(TrsTokenData.VARSDECSTART) ||
           token.getName().equals(TrsTokenData.SIGSTART) ||
           token.getName().equals(TrsTokenData.RULESDECSTART) ||
           token.getName().equals(TrsTokenData.COMMENTSTART);
  }

  // ========================= READING FUNCTION AND VARIABLE DECLARATIONS =========================

  /** 
   * varlist ::= VARSDECSTART IDENTIFIER* BRACKETCLOSE
   *
   * When presented with a varlist, this function reads the variables into the internally stored
   * symbol data.
   * Since varlists can only occur in UNSORTED TRSs, the variables are all stored to have the unit
   * sort ("o") as their type.
   *
   * @return true if the next token is VARSDECSTART and therefore the list was read; false if it is
   * not (in which case nothing is read, and data is not updated).
   */
  private boolean readVarList() {
    Token start = _status.readNextIf(TrsTokenData.VARSDECSTART);
    if (start == null) return false;
    while (true) {
      Token next = _status.nextToken();
      if (next.getName().equals(TrsTokenData.BRACKETCLOSE)) return true;
      if (next.getName().equals(TrsTokenData.IDENTIFIER)) {
        String name = next.getText();
        if (_symbols.lookupVariable(name) == null && _symbols.lookupFunctionSymbol(name) == null) {
          _symbols.addVariable(TermFactory.createVar(name));
        }
        else _status.storeError("Double declaration of variable " + name, next);
      }
      else {
        // error handling for incorrect tokens
        if (next.isEof()) {
          _status.storeError("Encountered end of input while reading varlist; no closing bracket " +
                             "given.", start);
          return true;
        }
        if (isSectionStart(next)) {
          _status.storeError("Unexpected " + next.getText() + " while reading varlist; did you " +
            "forget a closing bracket?", next);
          _status.pushBack(next);
          return true;
        }
        // if we encounter something else, it's unclear what the programmer did, so let's just
        // abort the parsing process
        _status.abort("Unexpected token: " + next.getText() + " (" + next.getName() +
          "); expected a variable name", next);
      }
    }
  }

  /**
   * type ::= IDENTIFIER* ARROW IDENTIFIER
   *
   * This function reads a sort declaration, and returns the corresponding type.
   * If the given input is not a sort declaration, then error recovery is done to construct a sort
   * declaration after all.  Hence, this cannot return null.
   */
  private Type readSortDeclaration() {
    Token next;
    ArrayList<BaseType> inputs = new ArrayList<BaseType>();
    while ((next = _status.readNextIf(TrsTokenData.IDENTIFIER)) != null) {
      inputs.add(TypeFactory.createSort(next.getText()));
    }
    _status.expect(TrsTokenData.ARROW, "IDENTIFIER (a sort) or the sort declaration arrow (->)");
    next = _status.expect(TrsTokenData.IDENTIFIER, "output sort");
    BaseType output;
    if (next != null) output = TypeFactory.createSort(next.getText());
    else if (inputs.size() == 0) output = TypeFactory.unitSort;
    else {
      output = inputs.get(inputs.size()-1);
      inputs.remove(inputs.size()-1);
    }
    return TypeFactory.createSortDeclaration(inputs, output);
  }

  /** 
   * fundec ::= BRACKETOPEN IDENTIFIER <integer> BRACKETCLOSE
   *          | BRACKETOPEN IDENTIFIER type BRACKETCLOSE
   *
   * This function reads a declaration, and returns the corresponding function symbol.
   * If the given text is not a function declaration, then an attempt at error recovery is done,
   * and if this fails, a ParseError thrown.  If no error is thrown, then this function returns a
   * function symbol, not null.  It is guaranteed that calling this advances the parsing status
   * (or causes an error to be thrown).
   */
  private FunctionSymbol readDeclaration() {
    // BRACKETOPEN IDENTIFIER
    boolean endwithbracket = (_status.expect(TrsTokenData.BRACKETOPEN,
                                             "an integer or sort declaration in brackets") != null);
    Token next = _status.expect(TrsTokenData.IDENTIFIER, "a function name");
    if (next == null) _status.throwCollectedErrors();
    String name = next.getText();
    if (_symbols.lookupVariable(name) != null) {
      _status.storeError("Function symbol " + name + " was previously declared as a variable.\n",
                         next);
    }
    if (_symbols.lookupFunctionSymbol(name) != null) {
      _status.storeError("Redeclaration of function symbol " + name + ".", next);
    }

    // make sure that we have the right kind of input to continue
    if (!_status.nextTokenIs(TrsTokenData.IDENTIFIER) &&
        !_status.nextTokenIs(TrsTokenData.ARROW)) {
      _status.abort("Unexpected token: expected either an integer (for the extended TRS " +
        "format), or a sort declaration (for the MSTRS format)", _status.peekNext());
    }

    // option 1: <integer> BRACKETCLOSE
    if (_status.nextTokensAre(new String[] { TrsTokenData.IDENTIFIER,TrsTokenData.BRACKETCLOSE })) {
      next = _status.nextToken();
      if (endwithbracket) _status.nextToken();  // skip past the BRACKETCLOSE
      try {
        int k = Integer.parseInt(next.getText());
        if (k < 0) {
          _status.storeError("Cannot set arity below 0.", next);
          k = 0;
        }
        return TermFactory.createConstant(name, k);
      }
      catch (NumberFormatException e) {
        _status.storeError("Unexpected identifier: " + next.getText() + ".  Expected an integer " +
          "(for the extended TRS format) or a sort declaration (for the MSTRS format).  Did you " +
          "forget ->?", next);
        return TermFactory.createConstant(name, TypeFactory.createSort(next.getText()));
      }
    }

    // option 2: type BRACKETCLOSE
    Type type = readSortDeclaration();
    if (endwithbracket) _status.expect(TrsTokenData.BRACKETCLOSE, "closing bracket");
    return TermFactory.createConstant(name, type);
  }

  /** 
   * funlist ::= SIGSTART fundec* BRACKETCLOSE
   *
   * When presented with a function symbol list, this method reads the function symbols into the
   * internally stored symbol data.
   *
   * Function lists in UNSORTED TRSs have declarations of the form BRACKETOPEN IDENTIFIER <integer>
   * BRACKETCLOSE.  Function lists in MANY-SORTED TRSs have declarations of the form
   * BRACKETOPEN IDENTIFIER type BRACKETCLOSE.  Here, we handle both at once, and also allow
   * mixing up declarations.
   *
   * @return true if the next token is SIGSTART and therefore the list was read; false if it is not
   * (in which case nothing is read, and the symbo ldata is not updated).
   */
  private boolean readSignature() {
    Token start = _status.readNextIf(TrsTokenData.SIGSTART);
    if (start == null) return false;
    while (true) {
      if (_status.readNextIf(TrsTokenData.BRACKETCLOSE) != null) return true;
      if (_status.peekNext().isEof()) {
        _status.storeError("Unexpected end of input while reading (SIG.", _status.peekNext());
        return true;
      }
      if (isSectionStart(_status.peekNext())) {
        _status.storeError("Unexpected " + _status.peekNext().getText() + "; did you forget ) " +
          "to close (SIG?", _status.peekNext());
        return true;
      }
      FunctionSymbol symbol = readDeclaration();
      if (!_symbols.symbolDeclared(symbol.queryName())) _symbols.addFunctionSymbol(symbol);
    }
  }

  // ======================================== READING TERMS =======================================

  /**
   * term = IDENTIFIER
   *      | IDENTIFIER BRACKETOPEN BRACKETCLOSE
   *      | IDENTIFIER BRACKETOPEN term (COMMA term)* BRACKETCLOSE
   *
   * When the current parsing status represents a term, this method reads it into a term structure,
   * which does not yet check correct typing / arity use of the term.
   */
  private TermStructure readTermStructure() {
    // first we should have an IDENTIFIER
    Token start = _status.expect(TrsTokenData.IDENTIFIER,
                                 "an identifier (variable or function name)");
    if (start == null) return null;
    TermStructure ret = new TermStructure(start);
    // if we don't follow up with a BRACKETOPEN, then that's enough
    if (_status.readNextIf(TrsTokenData.BRACKETOPEN) == null) return ret;
    // if we follow the BRACKETOPEN with a BRACKETCLOSE, then that's enough
    if (_status.readNextIf(TrsTokenData.BRACKETCLOSE) != null) return ret;
    // otherwise, start reading recursively
    while (true) {
      // read term
      TermStructure child = readTermStructure();
      if (child == null) ret.errored = true;
      else {
        ret.errored |= child.errored;
        ret.children.add(child);
      }
      // if we encounter BRACKETCLOSE, we have finished this term
      if (_status.readNextIf(TrsTokenData.BRACKETCLOSE) != null) return ret;
      // otherwise we must encounter COMMA followed by at least one more term
      if (_status.expect(TrsTokenData.COMMA, "a comma or closing bracket") == null) {
        // error situation: if they may have just forgotten a comma, pretend we saw one and
        // continue, but otherwise return what we already have
        ret.errored = true;
        if (!_status.nextTokenIs(TrsTokenData.IDENTIFIER)) return ret;
      }
    }
  }

  /**
   * This attempts to turn a TermStructure into a Term, using that all variables are necessarily
   * declared in the symbol data, and that function symbols may only be typed with first-order types
   * over the unit sort.  If function symbols are used with inconsistent arity, then an appropriate
   * error message is stored in the parser status.
   */
  private Term makeUnsortedTerm(TermStructure structure) {
    String name = structure.root.getText();

    int pos = _status.queryErrorPosition();
    
    // read and type all the children (and set error message for them if necessary)
    ArrayList<Term> children = new ArrayList<Term>();
    for (int i = 0; i < structure.children.size(); i++) {
      children.add(makeUnsortedTerm(structure.children.get(i)));
    }
    
    // term is a declared variable with no arguments
    Variable x = _symbols.lookupVariable(name);
    if (x != null && structure.children.size() == 0) return x;

    // term is a declared function symbol with the correct number of arguments
    FunctionSymbol f = _symbols.lookupFunctionSymbol(name);
    if (f != null && children.size() == f.queryArity()) {
      return TermFactory.createFunctionalTerm(f, children);
    }

    // term is an undeclared function symbol with 0 or more arguments
    if (x == null && f == null) {
      f = TermFactory.createConstant(name, children.size());
      _symbols.addFunctionSymbol(f);
      return TermFactory.createFunctionalTerm(f, children);
    }

    // error handling
    if (x != null) {  // variable with one or more arguments
      _status.storeError("Variable " + name + " used as root of a functional term.",
                         structure.root, pos);
      return x;
    }
    else {  // declared function symbol with wrong number of arguments
      _status.storeError("Function symbol " + name + " was previously used with " +
        f.queryArity() + " arguments, but is here used with " + children.size() + ".",
        structure.root, pos);
    }
    f = TermFactory.createConstant(name, children.size());
    return TermFactory.createFunctionalTerm(f, children);
  }

  /**
   * This attempts to turn a TermStructure into a Term, using that all function symbols are
   * necessarily declared in the symbol data.  If the given type is not null, then the term is
   * expected to be of that type (and this will be used to type previously unseen variables).
   * If the given type is null, and the type cannot be derived (which is the case if the term is a
   * variable), this is not stored as an error by itself, but left for the caller to deal with.
   * If function symbols are used with arity different from their declared arity, or types do not
   * match the declaration, then an appropriate error message is stored in the parser status.
   *
   * Regardless of errors, this is guaranteed to either throw a ParseError, or return a term of the
   * expected type (if any).  If the expected type is not given (null), then a type will be guessed.
   * but it will not be recorded since this is likely an error situation.
   */
  private Term makeSortedTerm(TermStructure structure, Type expectedType) {
    String name = structure.root.getText();
    FunctionSymbol root = _symbols.lookupFunctionSymbol(name);
    Variable x = _symbols.lookupVariable(name);
    ArrayList<Term> children = new ArrayList<Term>();
    int pos = _status.queryErrorPosition();

    // we have a function symbol of the right arity and output type
    if (root != null && root.queryArity() == structure.children.size()) {
      Type type = root.queryType();
      for (int i = 0; i < structure.children.size(); i++) {
        Type t = type.queryArrowInputType();
        children.add(makeSortedTerm(structure.children.get(i), t));
        type = type.queryArrowOutputType();
      }
      if (expectedType == null || type.equals(expectedType)) {
        return TermFactory.createApp(root, children);
      }
    }

    // we have a declared variable of the right type, and no children
    if (x != null && structure.children.size() == 0 &&
        (expectedType == null || x.queryType().equals(expectedType))) return x;

    // we have what appears to be an undeclared variable, and no children
    if (root == null && x == null && structure.children.size() == 0) {
      if (expectedType == null) return TermFactory.createVar(name);
        // should not occur when parsing rules or non-variable terms, but it might happen as part
        // of error handling; in this case, the new variable should not be stored in _symbols!
      x = TermFactory.createVar(name, expectedType);
      _symbols.addVariable(x);
      return x;
    }

    // error handling
    Token err = structure.root;

    // let's calculate the children, if we didn't do that already (and store errors for them)
    if (children.size() == 0) {
      for (int i = 0; i < structure.children.size(); i++) {
        children.add(makeSortedTerm(structure.children.get(i), null));
      }
    }

    // let's calculate a "fake root" symbol of the right type to construct the desired term (for
    // use in error message and the like)
    Type type = expectedType == null ? TypeFactory.unitSort : expectedType;
    for (int i = children.size()-1; i >= 0; i--) {
      type = TypeFactory.createArrow(children.get(i).queryType(), type);
    }
    FunctionSymbol fakeroot = TermFactory.createConstant(name, type);
    Term ret = TermFactory.createApp(fakeroot, children);

    // error: we have a function symbol of the right arity, but the wrong output type
    if (root != null && root.queryArity() == structure.children.size()) {
      _status.storeError("Expected term of type " + expectedType.toString() + ", but got term " +
        ret.toString() + " of type " + root.queryType().queryOutputSort().toString() + ".", err,
        pos);
    }

    // error: we have a function symbol of the wrong arity
    else if (root != null) {
      _status.storeError("Function symbol " + name + " was declared with " + root.queryArity() +
        " arguments, but is used here with " + structure.children.size() + ".", err, pos);
    }

    // error: we have a variable of the wrong type
    else if (x != null && structure.children.size() == 0) {
      _status.storeError("Expected term of type " + expectedType.toString() + ", but got " +
        "variable " + name + " which was previously used with type " + x.queryType().toString() +
        ".", err, pos);
    }

    // error: we have a variable applied to arguments
    else if (x != null) {
      _status.storeError("Variable " + name + " used as a function symbol!", err, pos);
    }

    // error: we have an undeclared symbol, but there are children!
    else {  // undeclared symbol, but there are children!
      _status.storeError("Undeclared function symbol: " + name + ".", err, pos);
    }

    return ret;
  }

  // ======================================== READING RULES =======================================

  /**
   * rule ::= term ARROW term
   * When the current parsing status represents a rule, this method reads it and returns the result.
   * If "sorted" is true, then the terms in the rule are typed assuming a many-sorted signature is
   * given for the function symbols.  If it is false, then the terms in the rule are typed assuming
   * the variables are all given in the symbol data.
   * If this returns null, reading the rule failed, but at least one character (the arrow) has been
   * read, and error recovery may still be doable; it might still be possible to read the next rule.
   * Otherwise, it will either throw a ParseError or return a valid rule.  (It is possible that some
   * errors will be stored in the status, however.)
   */
  private Rule readRule(boolean sorted) {
    TermStructure left = readTermStructure();
    if (_status.expect(TrsTokenData.ARROW, "ARROW (->)") == null) _status.throwCollectedErrors();
    TermStructure right = readTermStructure();
    if (left == null || left.errored || right == null || right.errored) return null;
    Term l, r;
    if (!sorted) {
      l = makeUnsortedTerm(left);
      r = makeUnsortedTerm(right);
    }
    else {
      l = makeSortedTerm(left, null);
      Type expected = l.queryType();
      if (l.isVariable()) {
        expected = null;
        _status.storeError("The left-hand side of a rule is not allowed to be a variable.",
          left.root);
      }
      r = makeSortedTerm(right, expected);
      _symbols.clearEnvironment();
    }

    try { return RuleFactory.createFirstOrderRule(l, r); }
    catch (IllegalRuleError e) {
      _status.storeError(e.queryProblem(), left.root);
      return null;
    }
  }

  /**
   * rules ::= RULESDECSTART rule* BRACKETCLOSE
   * The current status is expected to start with RULESDECSTART (if not, we store an error and
   * return the empty list).  We read and return the rules, or throw a ParseError if the rules list
   * is poorly shaped.
   */
  private ArrayList<Rule> readRules(boolean sorted) {
    ArrayList<Rule> ret = new ArrayList<Rule>();
    if (_status.expect(TrsTokenData.RULESDECSTART, "rules declaration") == null) return ret;
    while (_status.readNextIf(TrsTokenData.BRACKETCLOSE) == null) {
      Rule r = readRule(sorted);
      if (r != null) ret.add(r);
    }
    return ret;
  }

  // ===================================== READING A FULL TRS =====================================

  /**
   * comment ::= COMMENTOPEN string BRACKETCLOSE EOF
   * If the current status starts with COMMENTOPEN, we read until the end of the file and store an
   * error if the last bracket is not right before it; in this case we return true.
   * If it starts with something else, we return false and read nothing.
   */
  private boolean readComment() {
    Token start = _status.readNextIf(TrsTokenData.COMMENTSTART);
    if (start == null) return false;
    Token token = _status.nextToken();
    Token lastFollow = null;
    while (!token.isEof()) {
      if (token.getName().equals(TrsTokenData.BRACKETCLOSE)) {
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
  private TRS readTRS() {
    readVarList();
    boolean funsGiven = readSignature();
    ArrayList<Rule> rules = readRules(funsGiven);
    if (!readComment()) _status.expect(Token.EOF, "end of input");
    Alphabet alphabet = _symbols.queryCurrentAlphabet();
    return TRSFactory.createMSTRS(alphabet, rules);
  }

  // ============================= HELPER FUNCTIONALITY FOR UNIT TESTS ============================

  /**
   * Given a ParsingStatus of the form (VARS ...) ..., this reads the var list and returns the
   * corresponding symbol data.  The status is advanced just past the var list.
   * If the ParsingStatus does not have this form, then null is returned instead.
   */
  static SymbolData readVariableDeclaration(ParsingStatus ps) {
    TrsInputReader reader = new TrsInputReader(ps);
    if (reader.readVarList()) return reader._symbols;
    else return null;
  }

  /**
   * Given a ParsingStatus of the form (SIG ...) ..., this reads the signature and returns the
   * corresponding symbol data.  The status is advanced just past the signature
   * If the ParsingStatus does not have this form, then null is returned instead.
   */
  static SymbolData readSignature(ParsingStatus ps) {
    TrsInputReader reader = new TrsInputReader(ps);
    if (reader.readSignature()) return reader._symbols;
    else return null;
  }

  /**
   * Given a ParsingStatus of the form (RULES ...) ..., this reads the rules and returns them.
   * If sorted = true, then the terms are read as many-sorted terms; that is, data is assumed to
   * have declarations for all function symbols in the terms.  If sorted = false, then the terms
   * are read as unsorted terms; that is, data is assumed to have declarations x : o for all
   * variables in the terms.  If this fails, or other problems arise, errors are stored in the
   * status or a ParseError is thrown.
   */
  static ArrayList<Rule> readRules(ParsingStatus ps, SymbolData data, boolean sorted) {
    TrsInputReader reader = new TrsInputReader(ps);
    reader._symbols = data;
    return reader.readRules(sorted);
  }

  // ================================= FUNCTIONS FOR INTERNAL USE =================================

  /**
   * Reads the given term from string, given that all the variables in it are listed in vars.
   */
  public static Term readUnsortedTermFromString(String str, String vars) {
    str = "(VARS " + vars + ")\n" + str;
    ParsingStatus status = new ParsingStatus(TrsTokenData.getStringLexer(str), 10);
    TrsInputReader reader = new TrsInputReader(status);
    Term ret = null;
    if (reader.readVarList()) {
      TermStructure structure = reader.readTermStructure();
      if (structure != null && !structure.errored) {
        ret = reader.makeUnsortedTerm(structure);
      }
    }
    status.throwCollectedErrors();
    return ret;
  }

  /**
   * Reads the given term from string, given that all the function symbols in it are listed in sig.
   *
   * The expectedSort is allowed to be null.  The signature is not (use "" if no functions are
   * declared).
   */
  public static Term readSortedTermFromString(String str, String sig, BaseType expectedSort) {
    str = "(SIG " + sig + ")\n" + str;
    ParsingStatus status = new ParsingStatus(TrsTokenData.getStringLexer(str), 10);
    TrsInputReader reader = new TrsInputReader(status);
    Term ret = null;
    if (reader.readSignature()) {
      TermStructure structure = reader.readTermStructure();
      if (structure != null && !structure.errored) {
        ret = reader.makeSortedTerm(structure, expectedSort);
      }
    }
    status.throwCollectedErrors();
    return ret;
  }

  /**
   * Reads the given term from string, given that all the function symbols in it are listed in sig.
   */
  public static Term readSortedTermFromString(String str, String sig) {
    return readSortedTermFromString(str, sig, null);
  }

  /**
   * Reads the given term from string, given that all the function symbols in it are declared in
   * the alphabet of the given TRS.  This term should not be a variable, since then it will not be
   * possible to derive the type, and a ParseError will be thrown.
   */
  public static Term readTermFromString(String str, TRS trs) {
    ParsingStatus status = new ParsingStatus(TrsTokenData.getStringLexer(str), 10);
    TrsInputReader reader = new TrsInputReader(status, trs);
    TermStructure structure = reader.readTermStructure();
    Term ret = null;
    if (structure != null && !structure.errored) {
      ret = reader.makeSortedTerm(structure, null);
    }
    status.expect(Token.EOF, "end of string");
    status.throwCollectedErrors();
    return ret;
  }

  /**
   * Parses the given program, and returns the (sorted or unsorted) TRS that it defines.
   * If the string is not correctly formed, this may throw a ParseError.
   */
  public static TRS readTrsFromString(String str) {
    ParsingStatus status = new ParsingStatus(TrsTokenData.getStringLexer(str), 10);
    TrsInputReader reader = new TrsInputReader(status);
    TRS ret = reader.readTRS();
    status.throwCollectedErrors();
    return ret;
  }

  /**
   * Parses the given file, which should be a .trs or .mstrs file, into a many-sorted TRS.
   * This may throw a ParseError, or an IOException if something goes wrong with the file reading.
   */
  public static TRS readTrsFromFile(String filename) throws IOException {
    ParsingStatus status = new ParsingStatus(TrsTokenData.getFileLexer(filename), 10);
    TrsInputReader reader = new TrsInputReader(status);
    TRS ret = reader.readTRS();
    status.throwCollectedErrors();
    return ret;
  }
}

