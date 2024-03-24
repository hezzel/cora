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

package cora.reader;

import com.google.common.collect.ImmutableList;
import java.io.IOException;
import java.util.ArrayList;
import java.util.TreeSet;

import charlie.exceptions.IllegalRuleError;
import charlie.exceptions.ParseError;
import charlie.exceptions.UnexpectedPatternError;
import charlie.util.LookupMap;
import charlie.parser.lib.Token;
import charlie.parser.lib.ErrorCollector;
import charlie.parser.Parser;
import charlie.parser.Parser.*;
import charlie.parser.OCocoParser;
import charlie.types.*;
import charlie.terms.*;
import charlie.trs.*;

/**
 * This class reads text from string or file written in the .trs format that up until 2023 was used
 * by the international confluence competition; this is a simplification of the old human-readable
 * format of the international termination competition.
 * Specifically, interest is limited to MANYSORTED term rewriting systems.  Unsorted TRSs have the
 * same .trs extension, but should be handled through the OCocoUnsortedInputReader.
 * If a .trs file is given and it is unclear whether this is sorted or unsorted, use the
 * OCocoUnsortedInputREader to distinguish.
 */
public class OCocoSortedInputReader {
  /**
   * The reader keeps track of the declared variables, and the function symbols encountered so far.
   */
  private SymbolData _symbols;

  /** When the reader encounters errors, it stores them in this collector. */
  private ErrorCollector _errors;

  /**
   * Stores the parsing status for use by methods of the OCocoSortedInputReader class.
   * Private because it should only be called by the static methods that use a OCocoSortedInputReader.
   */
  private OCocoSortedInputReader(SymbolData data, ErrorCollector collector) {
    _symbols = data;
    _errors = collector;
  }

  private void storeError(String message, Token token) {
    _errors.addError(token.getPosition() + ": " + message);
  }

  // =============================== READING PARSERTERMS INTO TERMS ===============================

  /** 
   * This attempts to turn a ParserTerm into a Term, using that all function symbols are
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
  private Term makeTerm(ParserTerm pterm, Type expected) {
    FunctionSymbol f;
    Type texp = expected == null ? TypeFactory.defaultSort : expected;

    switch (pterm) {
      // base case: a constant or variable
      case Parser.Identifier(Token token, String name):
        Variable x = _symbols.lookupVariable(name);
        if (x != null && (expected == null || x.queryType().equals(expected))) return x;
        f = _symbols.lookupFunctionSymbol(name);
        if (f != null && expected == null && f.queryArity() == 0) return f;
        if (f != null && expected != null && f.queryType().equals(expected)) return f;
        if (x == null && f == null) {
          x = TermFactory.createVar(name, texp);
          if (expected != null) _symbols.addVariable(x);
          return x;
        }

        // error handling
        if (x != null) {  // variable of the wrong type
          storeError("Expected term of type " + expected.toString() + ", but got variable " + name +
            " that was previously used with type " + x.queryType() + ".", token);
        }
        else if (f.queryArity() == 0) {  // constant function symbol of the wrong type
          storeError("Expected term of type " + expected.toString() + ", but got constant symbol " +
            name + " of type " + f.queryType().toString() + ".", token);
        }
        else storeError("Illegal occurrence of unapplied function symbol " + name + "!", token);
        return TermFactory.createConstant(name, texp);

      // main case: a functional term f(s1,...,sn)
      case Parser.Application(Token token, Parser.Identifier(Token t2, String name),
                              ImmutableList<ParserTerm> args):
        f = _symbols.lookupFunctionSymbol(name);
        ArrayList<Term> children = new ArrayList<Term>();
        if (f != null && f.queryArity() == args.size() &&
            (expected == null || f.queryType().queryOutputType().equals(expected))) {
          Type t = f.queryType();
          for (int i = 0; t instanceof Arrow(Type inp, Type out); i++) {
            children.add(makeTerm(args.get(i), inp));
            t = out;
          }
          return TermFactory.createFunctionalTerm(f, children);
        }

        // error handling
        if (_symbols.lookupVariable(name) != null) {
          storeError("Variable " + name + " used as a function symbol!", token);
        }
        else if (f == null) storeError("Undeclared function symbol: " + name + ".", token);
        else if (f.queryArity() != args.size()) {
          storeError("Function symbol " + name + " was declared with " + f.queryArity() +
            " arguments, but is used here with " + args.size() + ".", token);
        }
        else {
          storeError("Expected term of type " + expected.toString() + ", but got functional term " +
            name + "(...) of type " + f.queryType().queryOutputType().toString() + ".", token);
          // parse the arguments with knowledge of what types they should have
          Type t = f.queryType();
          for (int i = 0; t instanceof Arrow(Type inp, Type out); i++) {
            children.add(makeTerm(args.get(i), inp));
            t = out;
          }
        }
        while (children.size() < args.size()) {
          children.add(makeTerm(args.get(children.size()), null));
        }
        Type t = expected;
        if (t == null) t = TypeFactory.defaultSort;
        for (int i = children.size()-1; i >= 0; i--) {
          t = TypeFactory.createArrow(children.get(i).queryType(), t);
        }
        f = TermFactory.createConstant(name, t);
        return TermFactory.createFunctionalTerm(f, children);
      
      default:
        throw new UnexpectedPatternError("OCocoSortedInputReader", "makeUnsortedTerm",
          "parser term " + pterm.toString(), "a variable or functional term");
    }
  }

  // ======================================= READING RULES ========================================

  /**
   * This turns a given parser rule into a Rule.
   * The function may return null if one of the sides of the rules has an error, or the rule is
   * invalid for some other reason.
   */
  private Rule makeRule(Parser.ParserRule rule) {
    ParserTerm left = rule.left();
    ParserTerm right = rule.right();

    if (left.hasErrors()) return null;
    Term l = makeTerm(left, null);
    if (l.isVariable()) {
      storeError("The left-hand side of a rule is not allowed to be a variable.", rule.token());
      if (!right.hasErrors()) makeTerm(right, null);    // for additional error messages
      return null;
    }
    // we only check this now, so we can still give type errors about the left-hand side
    if (right.hasErrors()) return null;
    Term r = makeTerm(right, l.queryType());
    
    _symbols.clearEnvironment();

    try { return TrsFactory.createRule(l, r, TrsFactory.MSTRS); }
    catch (IllegalRuleError e) {
      storeError(e.queryProblem(), rule.token());
      return null;
    }
  }

  // ===================================== READING A FULL TRS =====================================

  private TRS makeTRS(Parser.ParserProgram trs) {
    LookupMap<ParserDeclaration> decl = trs.fundecs();
    for (String name : decl.keySet()) {
      _symbols.addFunctionSymbol(TermFactory.createConstant(name, decl.get(name).type()));
    }   

    ArrayList<Rule> rules = new ArrayList<Rule>();
    for (ParserRule rule : trs.rules()) {
      Rule r = makeRule(rule);
      if (r != null) rules.add(r);
    }   
    Alphabet alphabet = _symbols.queryCurrentAlphabet();
    return TrsFactory.createTrs(alphabet, rules, TrsFactory.MSTRS);
  }

  // ==================================== PUBLIC FUNCTIONALITY ====================================

  /** Helper function for different readTerm functions. */
  private static Term readTerm(String str, SymbolData data, Base expectedSort) {
    ErrorCollector collector = new ErrorCollector();
    OCocoSortedInputReader rd = new OCocoSortedInputReader(data, collector);
    ParserTerm pterm = OCocoParser.readTerm(str, collector);
    Term ret = null;
    if (collector.queryErrorCount() == 0) ret = rd.makeTerm(pterm, expectedSort);
    if (collector.queryErrorCount() > 0) throw new ParseError(collector.queryCollectedMessages());
    return ret;
  }

  /**
   * Reads the given term from string, given that all the function symbols in it are listed in sig.
   *
   * The expectedSort is allowed to be null.  The signature is not (use "" if no functions are
   * declared).
   */
  public static Term readTerm(String str, String sig, Base expectedSort) {
    sig = "(SIG " + sig + ")\n";
    LookupMap<Parser.ParserDeclaration> decs = OCocoParser.readDeclarations(sig);
    SymbolData data = new SymbolData();
    for (String d : decs.keySet()) {
      data.addFunctionSymbol(TermFactory.createConstant(d, decs.get(d).type()));
    }
    return readTerm(str, data, expectedSort);
  }

  /**
   * Reads the given term from string, given that all the function symbols in it are listed in sig.
   * The term should not be a variable; if it is, a type is guessed.
   */
  public static Term readTerm(String str, String sig) {
    return readTerm(str, sig, null);
  }

  /**
   * Reads the given term from string, given that all the function symbols in it are declared in
   * the alphabet of the given TRS.  This term should not be a variable, since then it will not be
   * possible to derive the type, and a ParseError will be thrown.
   */
  public static Term readTerm(String str, TRS trs) {
    return readTerm(str, new SymbolData(trs), null);
  }

  /**
   * Helper function for readTrsFromString and readTrsFromFile, which is also used by
   * OCocoInputReader when a string is given where we do not know a priori if it is sorted or
   * unsorted.
   */
  static TRS readParserProgram(ParserProgram trs, ErrorCollector collector) {
    OCocoSortedInputReader rd = new OCocoSortedInputReader(new SymbolData(), collector);
    TRS ret = rd.makeTRS(trs);
    if (collector.queryErrorCount() > 0) throw new ParseError(collector.queryCollectedMessages());
    return ret;
  }

  /**
   * Parses the given program, and returns the (sorted or unsorted) TRS that it defines.
   * If the string is not correctly formed, this may throw a ParseError.
   */
  public static TRS readTrsFromString(String str) {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram trs = OCocoParser.readProgramFromString(str, collector);
    return readParserProgram(trs, collector);
  }

  /**
   * Parses the given file, which should be a .trs or .mstrs file, into a many-sorted TRS.
   * This may throw a ParseError, or an IOException if something goes wrong with the file reading.
   */
  public static TRS readTrsFromFile(String filename) throws IOException {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram trs = OCocoParser.readProgramFromFile(filename, collector);
    return readParserProgram(trs, collector);
  }
}
