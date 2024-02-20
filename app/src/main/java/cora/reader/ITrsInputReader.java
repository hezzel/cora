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
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Stack;

import cora.exceptions.*;
import cora.utils.LookupMap;
import cora.parser.lib.Token;
import cora.parser.lib.ErrorCollector;
import cora.parser.Parser;
import cora.parser.Parser.*;
import cora.parser.ITrsParser;
import cora.types.*;
import cora.terms.*;
import cora.trs.*;

/**
 * This class reads text from string or file written in the .itrs format that up until 2023 was used
 * by the international termination competition, category innermost integer term rewriting.
 *
 * Since this format is in principle untyped, types are derived (innermost termination of a TRS is
 * equivalent to innermost termination of a sorted TRS with the same erasure).
 */
public class ITrsInputReader {
  /** When the reader encounters errors, it stores them in this collector. */
  private ErrorCollector _errors;
  /**
   * As part of parsing, we will generate a graph whose nodes are the typeable positions (e.g.,
   * argument 2 of symbol f), and whose edges indicate when two nodes must have the same type.
   */
  private TreeMap<String,TreeSet<String>> _typeGraph = new TreeMap<String,TreeSet<String>>();
  /**
   * Eventually, we determine the types of all function symbols, which are stored in the symbol
   * data.  During the typing of rules, also the variables will temporarily be stored there.
   */
  private SymbolData _symbols;

  /**
   * Stores the error collector for use by methods of the ITrsInputReader class.
   * Private because it should only be called by the static methods that use a ITrsInputReader.
   */
  private ITrsInputReader(ErrorCollector collector) {
    _errors = collector;
    _typeGraph = null;    // don't use before calling generateTypeGraph
    _symbols = null;      // don't use before calling determineSymbolTypes
  }

  private void storeError(String message, Token token) {
    _errors.addError(token.getPosition() + ": " + message);
  }

  // ====================================== CHECKING ARITIES ======================================

  /**
   * As a first step of reading a TRS, we go over the whole thing and save the arities of
   * non-theory symbols, making sure that they are used consistently and saving errors if not.
   * This will also save errors if any of the theory symbols is used with the wrong arity, or a
   * variable is used as a function symbol.
   */
  private TreeMap<String,Integer> checkArities(ParserProgram trs) {
    TreeMap<String,Integer> ret = new TreeMap<String,Integer>();
    for (int i = 0; i < trs.rules().size(); i++) {
      ParserRule rule = trs.rules().get(i);
      LookupMap<ParserDeclaration> vars = rule.vars();
      Stack<ParserTerm> terms = new Stack<ParserTerm>();
      terms.push(rule.right());
      terms.push(rule.left());
      ParserTerm pt = rule.constraint();
      if (pt != null) terms.push(pt);
      while (!terms.isEmpty()) {
        ParserTerm s = terms.pop();
        switch (s) {
          case BoolVal(Token token, boolean istrue): continue;  // nothing to do
          case IntVal(Token token, int value): continue;        // nothing to do
          case Identifier(Token token, String name):
            checkFunctionalArities(token, name, ImmutableList.of(), vars, ret);
            continue;
          case Application(Token dummy, Identifier(Token token, String name),
                           ImmutableList<ParserTerm> args):
            for (int j = args.size()-1; j >= 0; j--) terms.push(args.get(j));
            checkFunctionalArities(token, name, args, vars, ret);
            continue;
          case Application(Token dummy, CalcSymbol(Token token, String name),
                           ImmutableList<ParserTerm> args):
            for (int j = args.size()-1; j >= 0; j--) terms.push(args.get(j));
            checkTheoryArities(token, name, args);
            continue;
          default:
            throw new UnexpectedPatternError("ITrsInputReader", "checkArities",
              "a variable or functional term", "parser term " + s.toString());
        }
      }
    }
    return ret;
  }

  /** Helper function for checkArities: checks a single term of the form f(s1,...,sn). */
  private void checkFunctionalArities(Token token, String fname, ImmutableList<ParserTerm> args,
                                      LookupMap<ParserDeclaration> vars,
                                      TreeMap<String,Integer> store) {
    // if it's a variable, it shouldn't be applied
    if (vars.containsKey(fname)) {
      if (args.size() != 0) {
        storeError("Variable " + fname + " occurs with arguments like a function symbol.", token);
      }
    }
    // if we haven't seen it before, it's a function symbol, and we store its arity
    else if (!store.containsKey(fname)) {
      store.put(fname, args.size());
    }
    // if we have seen it before, it had better occur with the expected number of arguments!
    else if (store.get(fname) != args.size()) {
      storeError("Function symbol " + fname + " occurs with " + args.size() + " arguments, " +
        "while it previously occurred with " + store.get(fname) + ".", token);
    }
  }

  /**
   * Helper function for checkArities: checks a single term of the form f(s1,...,sn) where f is
   * a calculation symbol.
   */
  private void checkTheoryArities(Token token, String fname, ImmutableList<ParserTerm> args) {
    if (fname.equals(ITrsParser.NOT)) {
      if (args.size() != 1) {
        storeError("Encountered negation with " + args.size() + " arguments (expected: 1).", token);
      }
    }
    else if (fname.equals(ITrsParser.MINUS)) {
      if (args.size() != 1 && args.size() != 2) {
        storeError("Encountered minus with " + args.size() + " arguments (expected: 1 or 2).",
          token);
      }
    }
    else {
      if (args.size() != 2) {
        storeError("Encountered " + fname + " with " + args.size() + " arguments (expected: 2).",
          token);
      }
    }
  }

  // ================================= COMPUTING TYPE DEPENDENCIES ================================

  /** Returns the node for argument index of symbol f (1 ≤ index ≤ arity(f). */
  private String funArgNode(String f, int index) {
    return "FUN." + f + "." + index;
  }

  /** Returns the node for the output type of symbol f. */
  private String funOutNode(String f) {
    return "FUN." + f + ".0";
  }

  /** Returns the node for the type of the given variable in the given rule. */
  private String varTypeNode(String varname, int rule) {
    return "VAR." + rule + "." + varname;
  }

  /** Returns the node for the unique integer type. */
  private String intNode() {
    return "INT";
  }

  /** Returns the node for the unique boolean type. */
  private String boolNode() {
    return "BOOL";
  }

  /** Ensures that the two given nodes become connected in the type dependency graph. */
  private void connect(String node1, String node2) {
    if (!_typeGraph.containsKey(node1)) _typeGraph.put(node1, new TreeSet<String>());
    if (!_typeGraph.containsKey(node2)) _typeGraph.put(node2, new TreeSet<String>());
    if (node1.equals(node2)) return;
    _typeGraph.get(node1).add(node2);
    _typeGraph.get(node2).add(node1);
  }

  /**
   * This returns the node for the output type of the given term, in the given rule.
   * Variables are recognised because they should all be declared in vars.
   */
  private String getTermOutputNode(ParserTerm term, int rule, LookupMap<ParserDeclaration> vars) {
    switch (term) {
      case BoolVal(Token token, boolean istrue):
        return boolNode();
      case IntVal(Token token, int value):
        return intNode();
      case Identifier(Token token, String name):
        if (vars.containsKey(name)) return varTypeNode(name, rule);
        else return funArgNode(name, 0);
      case Application(Token t1, Identifier(Token t2, String name), ImmutableList<ParserTerm> a):
        return funOutNode(name);
      case Application(Token t1, CalcSymbol(Token t2, String name), ImmutableList<ParserTerm> a):
        if (name.equals(ITrsParser.PLUS) || name.equals(ITrsParser.MINUS) ||
            name.equals(ITrsParser.TIMES) || name.equals(ITrsParser.DIV) ||
            name.equals(ITrsParser.MOD)) return intNode();
        else return boolNode();
      case PErr(ParserTerm t):
        return getTermOutputNode(t, rule, vars);
      default:
        throw new UnexpectedPatternError("ITrsInputReader", "getTermOutputNode",
          "a variable or functional term", "parser term " + term.toString());
    }
  }

  /** This function generates the type graph. */
  private void generateTypeGraph(ParserProgram trs, TreeMap<String,Integer> arities) {
    _typeGraph = new TreeMap<String,TreeSet<String>>();
    _typeGraph.put(intNode(), new TreeSet<String>());
    _typeGraph.put(boolNode(), new TreeSet<String>());

    for (int rule = 0; rule < trs.rules().size(); rule++) {
      ParserRule rho = trs.rules().get(rule);
      ParserTerm left = rho.left();
      ParserTerm right = rho.right();
      ParserTerm constr = rho.constraint();
      LookupMap<ParserDeclaration> vars = rho.vars();
      connect(getTermOutputNode(left, rule, vars), getTermOutputNode(right, rule, vars));
      if (constr != null) connect(boolNode(), getTermOutputNode(constr, rule, vars));
      Stack<ParserTerm> todo = new Stack<ParserTerm>();
      todo.push(left);
      todo.push(right);
      if (constr != null) todo.push(constr);
      while (!todo.isEmpty()) {
        ParserTerm t = todo.pop();
        if (!(t instanceof Application(Token x, ParserTerm h, ImmutableList<ParserTerm> a))) continue;
        for (ParserTerm u : a) todo.push(u);
        String base = null;
        if (h instanceof CalcSymbol(Token y, String name)) {
          if (name.equals(ITrsParser.AND) || name.equals(ITrsParser.OR) ||
              name.equals(ITrsParser.NOT)) base = boolNode();
          else base = intNode();
        }
        for (int i = 1; i <= a.size(); i++) {
          if (h instanceof Identifier(Token y, String name)) base = funArgNode(name, i);
          connect(base, getTermOutputNode(a.get(i-1), rule, vars));
        }
      }
    }
  }

  // ======================== DETERMINING THE TYPES OF ALL FUNCTION SYMBOLS =======================

  /** Returns all the nodes in the type dependency graph reachable from start */
  private TreeSet<String> floodfill(String start) {
    TreeSet<String> visited = new TreeSet<String>();
    Stack<String> todo = new Stack<String>();
    visited.add(start);
    todo.push(start);
    while (!todo.isEmpty()) {
      String node = todo.pop();
      for (String neighbour : _typeGraph.get(node)) {
        if (!visited.contains(neighbour)) {
          todo.push(neighbour);
          visited.add(neighbour);
        }
      }
    }
    return visited;
  }

  /**
   * Returns the type of the given node, given that the nodes in intNode have type Int, the nodes in
   * boolNodes have type Bool, and the rest have the default sort.
   */
  private Type determineNodeType(String node, TreeSet<String> intNodes, TreeSet<String> boolNodes) {
    if (intNodes.contains(node)) return TypeFactory.intSort;
    if (boolNodes.contains(node)) return TypeFactory.boolSort;
    return TypeFactory.unitSort;
  }

  /**
   * Determines the types of all function symbols, and stores it in the symbol data.
   * This assumes that generateTypeGraph has already been done.
   */
  private void determineSymbolTypes(TreeMap<String,Integer> arities) {
    TreeSet<String> intNodes = floodfill(intNode());
    TreeSet<String> boolNodes = floodfill(boolNode());
    if (intNodes.contains(boolNode())) {
      _errors.addError("I could not derive a valid typing (Int and Bool positions are not " +
        "consistentnly used).");
      return;
    }
    _symbols = new SymbolData();
    for (Map.Entry<String,Integer> entry : arities.entrySet()) {
      String f = entry.getKey();
      int arity = entry.getValue();
      Type type = determineNodeType(funOutNode(f), intNodes, boolNodes);
      for (int i = arity; i > 0; i--) {
        Type inp = determineNodeType(funArgNode(f, i), intNodes, boolNodes);
        type = TypeFactory.createArrow(inp, type);
      }
      _symbols.addFunctionSymbol(TermFactory.createConstant(f, type));
    }
  }

  // ====================================== TYPING ALL RULES ======================================

  /**
   * Reads the given parser term into a term.  This is guaranteed to return a term, not null.  (If
   * there are problems, an Error is thrown since there should not be any type issues if we get to
   * this point: this should have arisen when making the arities list of deriving types).
   */
  private Term makeTerm(ParserTerm term, Type expected) {
    FunctionSymbol f;

    switch (term) {
      case IntVal(Token t, int value):
        return TheoryFactory.createValue(value);
      case BoolVal(Token t, boolean isTrue):
        return TheoryFactory.createValue(isTrue);
      case Identifier(Token t, String name):
        f = _symbols.lookupFunctionSymbol(name);
        if (f != null) return f;
        Variable x = _symbols.lookupVariable(name);
        if (x != null) return x;
        if (expected == null) return TermFactory.createVar(name); // error is handled in caller
        x = TermFactory.createVar(name, expected);
        _symbols.addVariable(x);
        return x;
      case Application(Token token, ParserTerm head, ImmutableList<ParserTerm> args):
        f = readSymbol(head);
        ArrayList<Term> targs = new ArrayList<Term>();
        // a special case for minus, which can be used both in unary and binary notation in the
        // input, but is only supported in unary form within Cora
        boolean minus = false;
        if (f.equals(TheoryFactory.minusSymbol) && args.size() == 2) {
          f = TheoryFactory.plusSymbol;
          minus = true;
        }
        Type type = f.queryType();
        for (ParserTerm s : args) {
          switch (type) {
            case Arrow(Type inp, Type outp):
              targs.add(makeTerm(s, inp));
              type = outp;
              break;
            default: throw new TypingError("ITrsInputReader", "makeTerm", "function symbol f",
              f.queryType().toString(), "of arity " + args.size());
          }
        }
        if (minus) targs.set(1, TheoryFactory.minusSymbol.apply(targs.get(1)));
        return f.apply(targs);
      default:
        throw new UnexpectedPatternError("ITrsInputReader", "makeTerm",
          "a variable or functional term", "parser term " + term.toString());
    }
  }

  private FunctionSymbol readSymbol(ParserTerm term) {
    switch (term) {
      case Identifier(Token t, String name):
        FunctionSymbol f = _symbols.lookupFunctionSymbol(name);
        if (f == null) throw new Error("Somehow function symbol " + name + " is not declared.");
        return f;
      case CalcSymbol(Token t, String name):
        if (name.equals(ITrsParser.PLUS)) return TheoryFactory.plusSymbol;
        if (name.equals(ITrsParser.TIMES)) return TheoryFactory.timesSymbol;
        if (name.equals(ITrsParser.MINUS)) return TheoryFactory.minusSymbol;
        if (name.equals(ITrsParser.DIV)) return TheoryFactory.divSymbol;
        if (name.equals(ITrsParser.MOD)) return TheoryFactory.modSymbol;
        if (name.equals(ITrsParser.GREATER)) return TheoryFactory.greaterSymbol;
        if (name.equals(ITrsParser.SMALLER)) return TheoryFactory.smallerSymbol;
        if (name.equals(ITrsParser.GEQ)) return TheoryFactory.geqSymbol;
        if (name.equals(ITrsParser.LEQ)) return TheoryFactory.leqSymbol;
        if (name.equals(ITrsParser.EQUALS)) return TheoryFactory.equalSymbol;
        if (name.equals(ITrsParser.NEQ)) return TheoryFactory.distinctSymbol;
        if (name.equals(ITrsParser.AND)) return TheoryFactory.andSymbol;
        if (name.equals(ITrsParser.OR)) return TheoryFactory.orSymbol;
        if (name.equals(ITrsParser.NOT)) return TheoryFactory.notSymbol;
      default:
        throw new UnexpectedPatternError("ITrsInputReader", "readSymbol", "a declared identifier " +
          "or known calculation symbol", "parser term " + term.toString());
    }
  }

  /**
   * Reads the given rule.  If this does not result in a legal rule, null is returned and an error
   * stored.
   */
  private Rule makeRule(ParserRule rule) {
    _symbols.clearEnvironment();
    Term l = makeTerm(rule.left(), null);
    if (l.isVariable()) {
      storeError("The left-hand side of a rule is not allowed to be a variable.", rule.token());
      makeTerm(rule.right(), null);    // for additional error messages
      return null;
    }   
    Term r = makeTerm(rule.right(), l.queryType());
    Term constraint = null;
    if (rule.constraint() != null) constraint = makeTerm(rule.constraint(), null);

    try {
      if (constraint != null) return TrsFactory.createRule(l, r, constraint, TrsFactory.LCTRS);
      else return TrsFactory.createRule(l, r, TrsFactory.LCTRS);
    }
    catch (IllegalRuleError e) {
      storeError(e.queryProblem(), rule.token());
      return null;
    }
  }

  /** Once the symbol data is known, this function generates the TRS. */
  private TRS makeTRS(ParserProgram trs) {
    ArrayList<Rule> rules = new ArrayList<Rule>();
    for (ParserRule rho : trs.rules()) {
      Rule r = makeRule(rho);
      if (r != null) rules.add(r);
    }   
    Alphabet alphabet = _symbols.queryCurrentAlphabet();
    try { return TrsFactory.createTrs(alphabet, rules, TrsFactory.LCTRS); }
    catch (IllegalRuleError e) {
      _errors.addError(e.getMessage());
      return null;
    }
  }

  // ==================================== PUBLIC FUNCTIONALITY ====================================

  /** Helper function for readTrsFromString and readTrsFromFile */
  private static TRS readParserProgram(ParserProgram trs, ErrorCollector collector) {
    if (collector.queryErrorCount() > 0) throw new ParseError(collector.queryCollectedMessages());
    ITrsInputReader rd = new ITrsInputReader(collector);
    TreeMap<String,Integer> arities = rd.checkArities(trs);
    if (collector.queryErrorCount() > 0) throw new ParseError(collector.queryCollectedMessages());
    rd.generateTypeGraph(trs, arities);
    rd.determineSymbolTypes(arities);
    if (collector.queryErrorCount() > 0) throw new ParseError(collector.queryCollectedMessages());
    TRS ret = rd.makeTRS(trs);
    if (collector.queryErrorCount() > 0) throw new ParseError(collector.queryCollectedMessages());
    return ret;
  }

  /**
   * Parses the given program, and returns the integer TRS that it defines.
   * If the string is not correctly formed, or the system cannot be unambiguously typed as an
   * LCTRS, this may throw a ParseError.
   */
  public static TRS readTrsFromString(String str) {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram trs = ITrsParser.readProgramFromString(str, collector);
    return readParserProgram(trs, collector);
  }

  /**
   * Parses the given file, which should be a .itrs file, into an LCTRS.
   * This may throw a ParseError, or an IOException if something goes wrong with the file reading.
   */
  public static TRS readTrsFromFile(String filename) throws IOException {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram trs = ITrsParser.readProgramFromFile(filename, collector);
    return readParserProgram(trs, collector);
  }
}
