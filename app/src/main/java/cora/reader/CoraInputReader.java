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

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;

import com.google.common.collect.ImmutableList;
import cora.exceptions.*;
import cora.utils.LookupMap;
import cora.parser.lib.Token;
import cora.parser.lib.ErrorCollector;
import cora.parser.Parser.*;
import cora.parser.CoraParser;
import cora.types.*;
import cora.terms.*;
import cora.rewriting.*;

/**
 * This class reads text from string or file written in Cora's internal formalism(s).  Specific
 * restrictions are imposed depending on the exact type (e.g., constrained / unconstrained, and
 * applicative or with lambda / meta-variables).
 */
public class CoraInputReader extends TermTyper {
  public static final int MSTRS  = 1;
  public static final int STRS   = 2;
  public static final int CFS    = 3;
  public static final int AMS    = 4;
  public static final int LCTRS  = 5;
  public static final int LCSTRS = 6;
  public static final int CORA   = 7;

  /**
   * Stores the parsing status for use by methods of the CoraInputReader class.
   * Private because it should only be called by the static methods that use a CoraInputReader.
   */
  private CoraInputReader(SymbolData data, ErrorCollector collector) {
    super(data, collector);
  }

  // ==================================== READING DECLARATIONS ====================================

  /** This takes a mapping of parser declarations, and sorts it by token appearance. */
  private ArrayList<ParserDeclaration> sort(LookupMap<ParserDeclaration> decls) {
    ArrayList<ParserDeclaration> ret = new ArrayList<ParserDeclaration>(decls.values());
    Collections.sort(ret, new Comparator<ParserDeclaration>() {
      public int compare(ParserDeclaration t1, ParserDeclaration t2) {
        if (t1.token().before(t2.token())) return -1;
        else if (t1.token().getPosition().equals(t2.token().getPosition())) return 0;
        return 1;
      }
    });
    return ret;
  }

  /** takes a parser declaration and stores it as a function symbol declaration */
  private void handleFunctionDeclaration(ParserDeclaration decl) {
    if (decl == null || decl.type() == null) return;
    String name = decl.name();
    if (_symbols.lookupFunctionSymbol(name) != null) {
      storeError("Redeclaration of previously declared function symbol " + name + ".",
                 decl.token());
    }
    else _symbols.addFunctionSymbol(TermFactory.createConstant(name, decl.type()));
  }

  /** takes a set of parser declarations and stores them as variable declarations */
  private void readEnvironment(LookupMap<ParserDeclaration> vars) {
    for (ParserDeclaration decl : sort(vars)) {
      String name = decl.name();
      int arity = decl.extra();
      String kind = arity == 0 ? "variable" : "meta-variable";
      Type type = decl.type();
      if (_symbols.lookupFunctionSymbol(name) != null) {
        storeError("Name of " + kind + " " + name + " already occurs as a function symbol.",
          decl.token());
      }
      else if (_symbols.symbolDeclared(name)) {
        storeError("Redeclaration of " + kind + " " + name + " in the same environment.",
          decl.token());
      }
      else {
        if (arity == 0) _symbols.addVariable(TermFactory.createVar(name, type));
        else _symbols.addMetaVariable(TermFactory.createMetaVar(name, type, arity));
      }
    }
  }

  // ======================================= READING FULL TRSS ====================================

  /**
   * Either returns a valid rule, or returns null and potentially stores an erorr if the given
   * parser rule does not define a valid rule.
   */
  private Rule makeRule(ParserRule rule) {
    _symbols.clearEnvironment();
    readEnvironment(rule.vars());
    Term l = null, r = null, c = null;
    if (!rule.left().hasErrors()) l = makeTerm(rule.left(), null, true);
    if (!rule.right().hasErrors()) {
      Type expected = null;
      if (l != null) expected = l.queryType();
      r = makeTerm(rule.right(), expected, false);
    }
    if (rule.constraint() != null && !rule.constraint().hasErrors()) {
      c = makeTerm(rule.constraint(), TypeFactory.boolSort, true);
    }
    if (l == null || r == null) return null;
    
    try {
      if (c == null) return RuleFactory.createRule(l, r);
      else return RuleFactory.createRule(l, r, c);
    }
    catch (IllegalRuleError e) {
      storeError(e.queryProblem(), rule.token());
      return null;
    }
  }

  private TRS makeTRS(ParserProgram program, int kind) {
    // store the symbols into the symbol data
    for (ParserDeclaration decl : sort(program.fundecs())) {
      handleFunctionDeclaration(decl);
    }
    // go over the rules one by one
    ArrayList<Rule> rules = new ArrayList<Rule>();
    for (ParserRule rule : program.rules()) {
      Rule rho = makeRule(rule);
      if (rho != null) rules.add(rho);
    }

    // turn the result into a TRS!
    Alphabet alf = _symbols.queryCurrentAlphabet();
    try {
      // LCTRS, LCSTRS and CORA are constrained, the rest is not
      if (kind == MSTRS) return TRSFactory.createMSTRS(alf, rules);
      if (kind == LCTRS) return TRSFactory.createLCTRS(alf, rules);
      if (kind == STRS) return TRSFactory.createApplicativeTRS(alf, rules);
      if (kind == LCSTRS) return TRSFactory.createLCSTRS(alf, rules);
      if (kind == CFS) return TRSFactory.createCFS(alf, rules, false);
      if (kind == AMS) return TRSFactory.createAMS(alf, rules, false);
      return TRSFactory.createCoraTRS(_symbols.queryCurrentAlphabet(), rules, false);
    }
    catch (IllegalRuleError e) {
      _errors.addError(e.queryProblem());
    }
    catch (IllegalSymbolError e) {
      _errors.addError(e.queryProblem());
    }
    return null;
  }

  // =============================== ACCESS FUNCTIONS FOR UNIT TESTS ==============================

  /** Symbol declaration */
  static void readDeclarationForUnitTest(String str, SymbolData data, boolean constrained,
                                         ErrorCollector collector) {
    ParserDeclaration decl = CoraParser.readDeclaration(str, constrained, collector);
    CoraInputReader reader = new CoraInputReader(data, collector);
    reader.handleFunctionDeclaration(decl);
  }

  // ==================================== PUBLIC FUNCTIONALITY ====================================

  /**
   * Reads the given type from string.
   * If constrainedTRS is set to true, then Int, Bool and String are recognised as pre-defined
   * sorts, and identifiers are restricted as they are when reading a constrained TRS (e.g., sort
   * names may not contain "+").  If it is set to false, then identifiers are more general and
   * the pre-defined types will not be marked as theory sorts.
   */
  public static Type readType(String str, boolean constrainedTRS) {
    return CoraParser.readType(str, constrainedTRS, null);
  }

  /**
   * Reads the given type from string, recognising the pre-defined sorts.
   * This is the same as readTypeFromString(true).
   */
  public static Type readType(String str) {
    return CoraParser.readType(str);
  }

  /**
   * Reads the given term from string.
   * The TRS is used for its alphabet (function symbols are automatically recognised), and to
   * know whether or not we should include theories.  The rules and rule schemes are ignored.
   */
  public static Term readTerm(String str, TRS trs) {
    ErrorCollector collector = new ErrorCollector();
    ParserTerm pt = CoraParser.readTerm(str, trs.isConstrained(), collector);
    if (collector.queryErrorCount() > 0) throw new ParseError(collector.queryCollectedMessages());
    SymbolData data = new SymbolData(trs);
    CoraInputReader reader = new CoraInputReader(data, collector);
    Term ret = reader.makeTerm(pt, null, true);
    if (collector.queryErrorCount() > 0) throw new ParseError(collector.queryCollectedMessages());
    return ret;
  }

  /**
   * Reads the given term from string.
   * The TRS is used for its alphabet (function symbols are automatically recognised), and to
   * know whether or not we should include theories.  The rules and rule schemes are ignored.
   */
  public static Rule readRule(String str, TRS trs) {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = CoraParser.readRule(str, trs.isConstrained(), collector);
    if (collector.queryErrorCount() > 0) throw new ParseError(collector.queryCollectedMessages());
    SymbolData data = new SymbolData(trs);
    CoraInputReader reader = new CoraInputReader(data, collector);
    Rule ret = reader.makeRule(rule);
    if (collector.queryErrorCount() > 0) throw new ParseError(collector.queryCollectedMessages());
    return ret;
  } 

  /**
   * Parses the given program, and returns the TRS that it defines.
   * Here "kind" should be the kind of TRS (one of the constants defined at the head of the class).
   */
  public static TRS readTrsFromString(String str, int kind) {
    boolean constrained = kind == CORA || kind == LCTRS || kind == LCSTRS;
    ErrorCollector collector = new ErrorCollector();
    ParserProgram trs = CoraParser.readProgramFromString(str, constrained, collector);
    CoraInputReader reader = new CoraInputReader(new SymbolData(), collector);
    TRS ret = reader.makeTRS(trs, kind);
    if (collector.queryErrorCount() > 0) throw new ParseError(collector.queryCollectedMessages());
    return ret;
  }

  /**
   * Parses the given program, and returns the TRS that it defines.  This assumes the input is
   * the most permissive format currently supported.
   */
  public static TRS readTrsFromString(String str) {
    return readTrsFromString(str, CORA);
  }

  /** Reads the given file, parses the program in it, and returns the TRS that it defines. */
  public static TRS readTrsFromFile(String filename) throws IOException {
    ErrorCollector collector = new ErrorCollector();
    int kind = CORA;
    String extension =
      filename.substring(filename.lastIndexOf(".") + 1, filename.length()).toLowerCase();
    if (extension.equals("trs") || extension.equals("mstrs")) kind = MSTRS;
    else if (extension.equals("lctrs")) kind = LCTRS;
    else if (extension.equals("lcstrs")) kind = LCSTRS;
    else if (extension.equals("atrs") || extension.equals("strs")) kind = STRS;
    else if (extension.equals("cfs") || extension.equals("afs")) kind = CFS;
    else if (extension.equals("ams") || extension.equals("afsm")) kind = AMS;
    else if (!extension.equals("cora")) {
      collector.addError("Unexpected file extension: " + extension + ".  For default format, " +
        "use <filename>.cora");
    }
    boolean constrained = kind == CORA || kind == LCTRS || kind == LCSTRS;
    ParserProgram trs = CoraParser.readProgramFromFile(filename, constrained, collector);
    CoraInputReader reader = new CoraInputReader(new SymbolData(), collector);
    TRS ret = reader.makeTRS(trs, kind);
    if (collector.queryErrorCount() > 0) throw new ParseError(collector.queryCollectedMessages());
    return ret;
  }
}
