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

package charlie.reader;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;

import charlie.exceptions.*;
import charlie.util.LookupMap;
import charlie.types.*;
import charlie.parser.lib.Token;
import charlie.parser.lib.ErrorCollector;
import charlie.parser.Parser.*;
import charlie.parser.CoraParser;
import charlie.terms.*;
import charlie.trs.*;
import charlie.trs.TrsFactory.TrsKind;

/**
 * This class reads text from string or file written in Cora's internal formalism(s).  Specific
 * restrictions are imposed depending on the exact type (e.g., constrained / unconstrained, and
 * applicative or with lambda / meta-variables).
 */
public class CoraInputReader extends TermTyper {
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
    else {
      FunctionSymbol symbol = TermFactory.createConstant(name, decl.type());
      _symbols.addFunctionSymbol(symbol);
      if (decl.extra() == ParserDeclaration.EXTRA_PRIVATE) _symbols.setPrivate(symbol);
    }
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
   * Traditionally, fresh variables used in the right-hand side of a rule are used to model input
   * or random behaviour.  However, in most styles of TRSs in Charlie, this is not allowed. 
   * Instead, such variables should be included in the constraint.  Hence, we here do this move for
   * the user, allowing them to omit fresh variables from the constraint as syntactic sugar.
   *
   * (If the user wishes to actually specify a rule where the right-hand side contains a variable
   * that does not occur in the left or constraint, and that should not be considered a theory
   * variable, then this should be explicitly indicated.  There is currently no syntax for this,
   * but if the need arises such a syntax could be added in the future.)
   */
  private Term moveFreshVariablesIntoConstraint(Term left, Term right, Term constr, TrsKind kind,
                                                Token token) {
    for (Variable x : right.vars()) {
      if (left.freeReplaceables().contains(x)) continue;
      if (!x.queryType().isTheoryType() || !x.queryType().isBaseType()) {
        storeError("right-hand side of rule has a fresh variable " + x.queryName() + " of type " +
          x.queryType().toString() + " which does not occur on the left; only variables of " +
          "theory sorts may occur fresh (and that only in some kinds of TRSs).", token);
        continue;
      }
      if (constr == null) constr = TheoryFactory.createEquality(x, x);
      else if (!constr.freeReplaceables().contains(x)) {
        constr = TheoryFactory.createConjunction(constr, TheoryFactory.createEquality(x, x));
      }
    }
    return constr;
  }

  /**
   * Either returns a valid rule, or returns null and potentially stores an erorr if the given
   * parser rule does not define a valid rule.
   * Here, kind is allowed to be null.
   */
  private Rule makeRule(ParserRule rule, TrsKind kind) {
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

    if (kind == null || kind.theoriesIncluded()) {
      c = moveFreshVariablesIntoConstraint(l, r, c, kind, rule.left().token());
    }
    
    try {
      if (c == null && kind == null) return TrsFactory.createRule(l, r);
      else if (c == null) return TrsFactory.createRule(l, r, kind);
      else if (kind == null) return TrsFactory.createRule(l, r, c);
      else return TrsFactory.createRule(l, r, c, kind);
    }
    catch (IllegalRuleException e) {
      storeError(e.queryProblem(), rule.token());
      return null;
    }
  }

  private TRS makeTRS(ParserProgram program, TrsKind kind) {
    // store the symbols into the symbol data
    for (ParserDeclaration decl : sort(program.fundecs())) {
      handleFunctionDeclaration(decl);
    }
    // go over the rules one by one
    ArrayList<Rule> rules = new ArrayList<Rule>();
    for (ParserRule rule : program.rules()) {
      Rule rho = makeRule(rule, kind);
      if (rho != null) rules.add(rho);
    }

    // turn the result into a TRS!
    Alphabet alf = _symbols.queryCurrentAlphabet();
    try {
      return TrsFactory.createTrs(_symbols.queryCurrentAlphabet(), rules,
                                  _symbols.queryPrivateSymbols(), false, kind);
    }
    catch (IllegalRuleException e) {
      _errors.addError(e.queryProblem());
    }
    catch (IllegalSymbolException e) {
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

  /** Throws a ParseException if the given ErrorCollector has errors. */
  private static void throwIfErrors(ErrorCollector collector) {
    if (collector.queryErrorCount() > 0) {
      throw new ParseException(collector.queryCollectedMessages());
    }
  }

  /**
   * Reads the given term from string.
   * The TRS is used for its alphabet (function symbols are automatically recognised), and to
   * know whether or not we should include theories.  The rules and rule schemes are ignored.
   * Variables are declared as needed.  Note that reading a single variable will not succeed,
   * since its type cannot be derived.
   */
  public static Term readTerm(String str, TRS trs) {
    ErrorCollector collector = new ErrorCollector();
    ParserTerm pt = CoraParser.readTerm(str, trs.theoriesIncluded(), collector);
    throwIfErrors(collector);
    SymbolData data = new SymbolData(trs);
    CoraInputReader reader = new CoraInputReader(data, collector);
    Term ret = reader.makeTerm(pt, null, true);
    throwIfErrors(collector);
    return ret;
  }

  /**
   * This sets up a new SymbolData for the given TRS, with the variables and meta-variables in
   * naming already included (by their renamed names).
   */
  private static SymbolData setupSymbolData(TRS trs, Renaming naming) {
    SymbolData data = new SymbolData(trs);
    for (Replaceable r : naming.domain()) {
      String name = naming.getName(r);
      if (r instanceof Variable x) data.addVariable(x, name);
      else if (r instanceof MetaVariable z) data.addMetaVariable(z, name);
      else {
        throw new UnexpectedPatternException("CoraInputReader", "setupSymbolData",
          "replaceable " + name, "either a variable or a meta-variable");
      }
    }
    return data;
  }

  /**
   * Helper function for readTerm (multiple instances).  This function updates the given renaming
   * by giving all variables that occur in t but not yet in naming their own name.
   * This should work as expected if the given renaming was used when reading the term, and the
   * only blocked function symbols in the renaming are either not valid identifiers, or are the
   * names of function symbols in the TRS that was used to read the term.
   * If this is not the case, it may be that some variable was given an illegal default name; in
   * this case, an error is stored in the collector since this is unexpected bheaviour.
   */
  private static void updateRenaming(Renaming naming, Term t, ErrorCollector collector) {
    for (Replaceable r : t.freeReplaceables()) {
      if (naming.getName(r) == null) {
        if (!naming.setName(r, r.queryName())) {
          collector.addError("(meta-)variable " + r.queryName() + " is not allowed " +
            "for a variable in the given naming scheme");
        }
      }
    }
  }

  /**
   * Reads the given term from string.
   * The given renaming is used to recognise variables and meta-variables.  If updateRenaming is
   * true, it is also updated to set the names of new variables and meta-variables to their
   * actual names (provided this is allowed by the renaming; if not, this gives a parser exception).
   * The TRS is used for its alphabet (function symbols are automatically recognised), and to
   * know whether or not we should include theories.  The rules and rule schemes are ignored.
   */
  public static Term readTerm(String str, Renaming naming, boolean updateNaming, TRS trs) {
    ErrorCollector collector = new ErrorCollector();
    ParserTerm pt = CoraParser.readTerm(str, trs.theoriesIncluded(), collector);
    throwIfErrors(collector);
    SymbolData data = setupSymbolData(trs, naming);
    CoraInputReader reader = new CoraInputReader(data, collector);
    Term ret = reader.makeTerm(pt, null, true);
    if (ret != null && updateNaming) updateRenaming(naming, ret, collector);
    throwIfErrors(collector);
    return ret;
  }

  /**
   * Reads the given parser term into a proper term, using the TRS to assess the function symbols
   * (and to know if theory symbols should be created), and the Renaming to map (meta-)variable
   * names to (meta-)variables.
   *
   * It is allowed for the parser term to contain variable identifiers that are not yet in the
   * given renaming.  These will be added to the renaming (so the naming should be expected to be
   * altered).
   */
  public static Term readTerm(ParserTerm pt, Renaming naming, TRS trs) {
    ErrorCollector collector = new ErrorCollector();
    SymbolData data = setupSymbolData(trs, naming);
    CoraInputReader reader = new CoraInputReader(data, collector);
    Term ret = reader.makeTerm(pt, null, true);
    if (ret != null) updateRenaming(naming, ret, collector);
    throwIfErrors(collector);
    return ret;
  }

  /**
   * Reads the given term from string.
   * The TRS is used for its alphabet (function symbols are automatically recognised), and to
   * know whether or not we should include theories.  The rules and rule schemes are ignored.
   */
  public static Rule readRule(String str, TRS trs) {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = CoraParser.readRule(str, trs.theoriesIncluded(), collector);
    throwIfErrors(collector);
    SymbolData data = new SymbolData(trs);
    CoraInputReader reader = new CoraInputReader(data, collector);
    Rule ret = reader.makeRule(rule, null);
    throwIfErrors(collector);
    return ret;
  } 

  /**
   * Parses the given program, and returns the TRS that it defines.
   * Here "kind" should be the kind of TRS (one of the constants defined at the head of the class).
   */
  public static TRS readTrsFromString(String str, TrsKind kind) {
    boolean constrained = kind.theoriesIncluded();
    ErrorCollector collector = new ErrorCollector();
    ParserProgram trs = CoraParser.readProgramFromString(str, constrained, collector);
    CoraInputReader reader = new CoraInputReader(new SymbolData(), collector);
    TRS ret = reader.makeTRS(trs, kind);
    throwIfErrors(collector);
    return ret;
  }

  /**
   * Parses the given program, and returns the TRS that it defines.  This assumes the input is
   * the most permissive format currently supported.
   */
  public static TRS readTrsFromString(String str) {
    return readTrsFromString(str, TrsFactory.CORA);
  }

  /** Reads the given file, parses the program in it, and returns the TRS that it defines. */
  public static TRS readTrsFromFile(String filename) throws IOException {
    ErrorCollector collector = new ErrorCollector();
    TrsKind kind = TrsFactory.CORA;
    String extension =
      filename.substring(filename.lastIndexOf(".") + 1, filename.length()).toLowerCase();
    if (extension.equals("trs") || extension.equals("mstrs")) kind = TrsFactory.MSTRS;
    else if (extension.equals("lctrs")) kind = TrsFactory.LCTRS;
    else if (extension.equals("lcstrs")) kind = TrsFactory.LCSTRS;
    else if (extension.equals("atrs") || extension.equals("strs")) kind = TrsFactory.STRS;
    else if (extension.equals("cfs") || extension.equals("afs")) kind = TrsFactory.CFS;
    else if (extension.equals("ams") || extension.equals("afsm")) kind = TrsFactory.AMS;
    else if (!extension.equals("cora")) {
      collector.addError("Unexpected file extension: " + extension + ".  For default format, " +
        "use <filename>.cora");
    }
    boolean constrained = kind.theoriesIncluded();
    ParserProgram trs = CoraParser.readProgramFromFile(filename, constrained, collector);
    CoraInputReader reader = new CoraInputReader(new SymbolData(), collector);
    TRS ret = reader.makeTRS(trs, kind);
    throwIfErrors(collector);
    return ret;
  }
}
