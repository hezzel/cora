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

import com.google.common.collect.ImmutableList;
import java.io.IOException;
import java.util.ArrayList;

import charlie.exceptions.IllegalRuleException;
import charlie.exceptions.UnexpectedPatternException;
import charlie.util.FixedList;
import charlie.util.LookupMap;
import charlie.types.*;
import charlie.parser.lib.Token;
import charlie.parser.lib.ParsingErrorMessage;
import charlie.parser.lib.ErrorCollector;
import charlie.parser.lib.ParsingException;
import charlie.parser.Parser;
import charlie.parser.Parser.*;
import charlie.parser.OCocoParser;
import charlie.terms.*;
import charlie.trs.*;

/**
 * This class reads text from string or file written in the .trs format that up until 2023 was used
 * by the international confluence competition; this is a simplification of the old human-readable
 * format of the international termination competition.
 * Specifically, interest is limited to UNSORTED term rewriting systems.  Many-sorted TRSs have the
 * same .trs extension, but should be handled through the OCocoSortedInputReader.
 * If a .trs file is given and it is unclear whether this is sorted or unsorted, use the
 * OCocoUnsortedInputREader to distinguish.
 */
public class OCocoUnsortedInputReader {
  /**
   * The reader keeps track of the declared variables, and the function symbols encountered so far.
   */
  private SymbolData _symbols;

  /** When the reader encounters errors, it stores them in this collector. */
  private ErrorCollector _errors;

  /**
   * Stores the parsing status for use by methods of the OCocoUnsortedInputReader class.
   * Private because it should only be called by the static methods that use a OCocoUnsortedInputReader.
   */
  private OCocoUnsortedInputReader(SymbolData data, ErrorCollector collector) {
    _symbols = data;
    _errors = collector;
  }

  private void storeError(Token token, String message) {
    _errors.addError(new ParsingErrorMessage(token, message));
  }

  // =============================== READING PARSERTERMS INTO TERMS ===============================

  /**
   * This attempts to turn a ParserTerm into a Term, using that all variables are necessarily
   * declared in the symbol data, and that function symbols may only be typed with first-order types
   * over the default sort.  If function symbols are used with inconsistent arity, then an
   * appropriate error message is stored in the error collector.
   *
   * Regardless of errors, this is guaranteed to return a term.
   */
  private Term makeTerm(ParserTerm pterm) {
    Token token;
    String name;
    ImmutableList<ParserTerm> args;

    switch (pterm) {
      case Identifier(Token t, String n):
        token = t;
        name = n;
        args = ImmutableList.of();
        break;
      case Application(Token t1, Identifier(Token t2, String n), ImmutableList<ParserTerm> a):
        token = t1;
        name = n;
        args = a;
        break;
      default:
        throw new UnexpectedPatternException("OCocoUnsortedInputReader", "makeTerm",
          "parser term " + pterm.toString(), "a variable or functional term");
    }

    // the head is a declared variable
    Variable x = _symbols.lookupVariable(name);
    if (x != null) {
      if (args.size() == 0) return x;
      storeError(token, "Variable " + name + " used as root of a functional term.");
    }

    // otherwise, the head must be a function symbol
    FunctionSymbol f = _symbols.lookupFunctionSymbol(name);
    if (f == null) {
      f = TermFactory.createConstant(name, args.size());
      _symbols.addFunctionSymbol(f);
    }
    else if (f.queryArity() != args.size()) {
      storeError(token, "Function symbol " + name + " was previously used with " +
        f.queryArity() + " arguments, but is here used with " + args.size() + ".");
      f = TermFactory.createConstant(name, args.size());
    }

    // read and type all the children (and set error messages for them if necessary)
    ArrayList<Term> children = new ArrayList<Term>();
    for (int i = 0; i < args.size(); i++) children.add(makeTerm(args.get(i)));
    return TermFactory.createFunctionalTerm(f, children);
  }

  // ======================================= READING RULES ========================================

  /**
   * This turns a given parser rule into a Rule.
   * The function may return null if one of the sides of the rules has an error, or the rule is
   * invalid for some other reason.
   */
  private Rule makeRule(ParserRule rule) {
    LookupMap<ParserDeclaration> vars = rule.vars();
    ParserTerm left = rule.left();
    ParserTerm right = rule.right();

    _symbols.clearEnvironment();
    for (String name : vars.keySet()) {
      Variable x = TermFactory.createVar(name, vars.get(name).type());
      if (_symbols.lookupFunctionSymbol(name) != null) {
        storeError(vars.get(name).token(), "Duplicate symbol: " + name + " occurs both as a " +
          "variable and as a function symbol!");
        // let's not keep giving this error for every rule; just give up
        throw _errors.generateException();
      }
      _symbols.addVariable(x);
    }

    if (left.hasErrors()) return null;
    Term l = makeTerm(left);
    // we only check this now, so we can still give arity errors about the left-hand side
    if (right.hasErrors()) return null;
    Term r = makeTerm(right);

    try { return TrsFactory.createRule(l, r, TrsFactory.MSTRS); }
    catch (IllegalRuleException e) {
      storeError(rule.token(), e.queryProblem());
      return null;
    }
  }

  // ===================================== READING A FULL TRS =====================================

  private Boolean isUnsorted(Type t) {
    switch (t) {
      case Base(String n):
        return t.equals(TypeFactory.defaultSort);
      case Arrow(Type a, Type b):
        return isUnsorted(a) && isUnsorted(b);
      case Product(FixedList<Type> args):
        return false;
    }
  }

  /** Transforms a ParserProgram representing an unsorted TRS into a real TRS. */
  private TRS makeTRS(ParserProgram trs) {
    LookupMap<ParserDeclaration> decl = trs.fundecs();
    boolean problems = false;
    for (String name : decl.keySet()) {
      Type t = decl.get(name).type();
      if (!isUnsorted(t)) {
        storeError(decl.get(name).token(),
                   "Many-sorted function symbol " + name + " cannot occur in an unsorted TRS.");
        problems = true;
      }
      _symbols.addFunctionSymbol(TermFactory.createConstant(name, t));
    }
    if (problems) return null;

    ArrayList<Rule> rules = new ArrayList<Rule>();
    for (ParserRule rule : trs.rules()) {
      Rule r = makeRule(rule);
      if (r != null) rules.add(r);
    }
    Alphabet alphabet = _symbols.queryCurrentAlphabet();
    if (!decl.isEmpty()) {  // if at least one function symbol is declared, they should all be!
      for (FunctionSymbol f : alphabet.getSymbols()) {
        if (!decl.containsKey(f.queryName())) {
          storeError(null, "Undeclared function symbol (not allowed when SIG is given): " +
                           f.queryName());
        }
      }
    }
    return TrsFactory.createTrs(alphabet, rules, TrsFactory.MSTRS);
  }

  // ==================================== PUBLIC FUNCTIONALITY ====================================

  /**
   * Reads the given term from string, given that all the variables in it are listed in vars.
   * @throws ParsingException if either parsing or typing failed.
   */
  public static Term readTerm(String str, String vars) {
    ErrorCollector collector = new ErrorCollector();
    vars = "(VAR " + vars + ")";
    LookupMap<Parser.ParserDeclaration> decs = OCocoParser.readDeclarations(vars, collector);
    ParserTerm pterm = OCocoParser.readTerm(str, collector);
    SymbolData data = new SymbolData();
    for (String v : decs.keySet()) data.addVariable(TermFactory.createVar(v, decs.get(v).type()));
    OCocoUnsortedInputReader rd = new OCocoUnsortedInputReader(data, collector);
    Term ret = null;
    if (collector.queryErrorCount() == 0) ret = rd.makeTerm(pterm);
    // NOT using else here, because errors may also arise from makeUnsortedTerm!
    if (collector.queryErrorCount() > 0) throw collector.generateException();
    return ret;
  }

  /**
   * Helper function for readTrsFromString and readTrsFromFile, and for the same functions in
   * OCocoInputReader.
   */
  static TRS readParserProgram(ParserProgram trs, ErrorCollector collector) {
    OCocoUnsortedInputReader rd = new OCocoUnsortedInputReader(new SymbolData(), collector);
    TRS ret = rd.makeTRS(trs);
    if (collector.queryErrorCount() > 0) throw collector.generateException();
    return ret;
  }

  /**
   * Parses the given program, and returns the unsorted TRS that it defines.
   * If the string is not correctly formed, this may throw a ParsingException.
   */
  public static TRS readTrsFromString(String str) {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram trs = OCocoParser.readProgramFromString(str, collector);
    return readParserProgram(trs, collector);
  }

  /**
   * Parses the given file, which should be a .trs or .mstrs file, into a many-sorted TRS.
   * This may throw a ParsingException, or an IOException if something goes wrong with the file
   * reading.
   */
  public static TRS readTrsFromFile(String filename) throws IOException {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram trs = OCocoParser.readProgramFromFile(filename, collector);
    return readParserProgram(trs, collector);
  }
}
