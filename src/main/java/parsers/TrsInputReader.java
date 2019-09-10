/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.parsers;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.Token;

import cora.exceptions.ParserException;
import cora.exceptions.DeclarationException;
import cora.exceptions.TypingException;
import cora.exceptions.IllegalRuleError;
import cora.interfaces.types.Type;
import cora.interfaces.types.BaseType;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Variable;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.rewriting.TRS;
import cora.types.Sort;
import cora.types.ArrowType;
import cora.terms.UserDefinedSymbol;
import cora.terms.Var;
import cora.terms.FunctionalTerm;
import cora.rewriting.FirstOrderRule;
import cora.rewriting.TermRewritingSystem;

/**
 * This class reads text from string or file written in the .trs or .mstrs formats from the
 * international confluence competition.
 */
public class TrsInputReader extends InputReader {
  private static Type unitSort = new Sort("o");
  
  public TrsInputReader() {
    super(TrsParser.VOCABULARY, TrsParser.ruleNames);
  }

  /* ========== READING FUNCTION AND VARIABLE DECLARATIONS ========== */

  /**
   * Given that the tree represents a varlist, this function updates data with all the provided
   * variable declarations.
   * Since varlists can only occur in UNSORTED TRSs, the variables are all stored to have the unit
   * sort ("o") as their type.
   * (Note: only public for unit testing.)
   */
  public void handleVarList(ParseTree tree, ParseData data) throws ParserException {
    int k = tree.getChildCount()-1;
    verifyChildIsToken(tree, 0, "VARSDECSTART", "the start of a variable list: (VAR");
    verifyChildIsToken(tree, k, "BRACKETCLOSE", "a closing bracket ')'");
    for (int i = 1; i < k; i++) {
      verifyChildIsToken(tree, i, "IDENTIFIER", "a variable name (an identifier)");
      String name = tree.getChild(i).getText();
      if (data.lookupVariable(name) != null) {
        throw new ParserException(firstToken(tree), "Double declaration of variable " + name);
      }
      data.addVariable(new Var(name, unitSort));
    }
  }

  /**
   * This function takes an IDENTIFIER, which must be a integer; if the integer is k, then the type
   * o->...->o->o is returned, with in total k+1 "o"s (so k input arguments), where "o" is the unit
   * sort.
   * If the identifier is not an integer, a ParserException is thrown.
   */
  private Type readIntegerType(ParseTree tree) throws ParserException {
    int k;
    try { k = Integer.parseInt(tree.getText()); }
    catch (NumberFormatException e) {
      throw new ParserException(firstToken(tree), "Unexpected identifier '" + tree.getText() +
                                                  "; expected an integer!");
    }
    Type ret = unitSort;
    for (int i = 0; i < k; i++) ret = new ArrowType(unitSort, ret);
    return ret;
  }

  /**
   * Reads a type of the form sort1...sortN -> outputsort, or an integer k; the integer is turned
   * into the type o1...ok -> o, where "o" is a sort.
   * (Note: only public for unit testing.)
   */
  public Type readTypeOrArity(ParseTree tree) throws ParserException {
    if (tree.getChildCount() == 1) {
      verifyChildIsToken(tree, 0, "IDENTIFIER", "an integer identifier");
      return readIntegerType(tree.getChild(0));
    }
    int k = tree.getChildCount()-2;
    verifyChildIsToken(tree, k, "ARROW", "a type arrow");
    verifyChildIsToken(tree, k+1, "IDENTIFIER", "an identifier (the output sort)");
    String output = tree.getChild(k+1).getText();
    Type result = new Sort(output);
    for (int i = k-1; i >= 0; i--) {
      verifyChildIsToken(tree, i, "IDENTIFIER", "an identifier (an argument sort)");
      String arg = tree.getChild(i).getText();
      result = new ArrowType(new Sort(arg), result);
    }
    return result;
  }

  /**
   * Given that tree represents a single function declaration, this function updates data with the
   * new declaration.
   */
  private void handleDeclaration(ParseTree tree, ParseData data) throws ParserException {
    verifyChildIsToken(tree, 0, "BRACKETOPEN", "an opening bracket '('");
    verifyChildIsToken(tree, 1, "IDENTIFIER", "an identier (a function name)");
    verifyChildIsRule(tree, 2, "typeorarity", "an integer or a sort declaration");
    verifyChildIsToken(tree, 3, "BRACKETCLOSE", "a closing bracket ')'");

    String funname = tree.getChild(1).getText();
    Type type = readTypeOrArity(tree.getChild(2));

    if (data.lookupFunctionSymbol(funname) != null) {
      throw new ParserException(firstToken(tree), "Double declaration of " + funname);
    }
    if (data.lookupVariable(funname) != null) {
      throw new ParserException(firstToken(tree), "Function symbol " + funname +
                                                  " was previously declared as a variable.");
    }
    data.addFunctionSymbol(new UserDefinedSymbol(funname, type));
  }

  /**
   * Given that the tree represents a siglist, this function updates data with all the provided
   * declarations.
   */
  public void handleSignature(ParseTree tree, ParseData data) throws ParserException {
    int k = tree.getChildCount()-1;
    verifyChildIsToken(tree, 0, "SIGSTART", "the start of a signature: (SIG");
    verifyChildIsToken(tree, k, "BRACKETCLOSE", "a closing bracket ')'");
    for (int i = 1; i < k; i++) {
      verifyChildIsRule(tree, i, "fundec", "a function declaration");
      handleDeclaration(tree.getChild(i), data);
    }
  }

  /* ========== READING TERMS AND RULES ========== */

  /**
   * This function reads an identifier from the parse tree that should be either a variable or a
   * constant function symbol with the expected type.
   * If the symbol is already declared as a variable or function symbol, then the corresponding
   * symbol will be returned (if this does not give a type conflict with expectedType).  Otherwise:
   * - if mstrs is true, then all function symbols should have been declared; therefore, the symbol
   *   will then be considered a variable, and declared to have the expected type (if expectedType
   *   is null, a DeclarationException is thrown);
   * - if mstrs is false, then all variables should have been declared; the symbol will be
   *   considered a constant function symbol, and declared to have type o (the unit type).
   */
  private Term readConstantOrVariable(ParseTree tree, ParseData data, Type expectedType,
                                      boolean mstrs) throws ParserException {
    String name = tree.getText();

    // if it's declared as a variable or function symbol, return that (if there's no tpye conflict)
    Term ret = data.lookupVariable(name);
    if (ret == null) ret = data.lookupFunctionSymbol(name);
    if (ret != null) {
      if (expectedType != null && !ret.queryType().equals(expectedType)) {
        throw new TypingException(firstToken(tree), name, ret.queryType().toString(),
                                  expectedType.toString());
      }
      return ret;
    }

    // otherwise, it all depends on whether we are examining a trs or mstrs
    if (mstrs) {
      if (expectedType == null) throw new DeclarationException(firstToken(tree), name);
      Var x = new Var(name, expectedType);
      data.addVariable(x);
      return x;
    }
    else {
      if (expectedType != null && !expectedType.equals(unitSort)) {
        throw new TypingException(firstToken(tree), name, unitSort.toString(),
                                  expectedType.toString());
      }
      UserDefinedSymbol f = new UserDefinedSymbol(name, unitSort);
      data.addFunctionSymbol(f);
      return f;
    }
  }

  /**
   * This function reads a termlist into an arraylist of parse trees, each of which points to a
   * parsetree of kind "term".
   * All encountered terms are added onto the back of lst.
   */
  private void readTermList(ParseTree termlisttree, ArrayList<ParseTree> lst) {
    while (true) {
      verifyChildIsRule(termlisttree, 0, "term", "a term");
      lst.add(termlisttree.getChild(0));
      if (termlisttree.getChildCount() == 1) return;
      verifyChildIsToken(termlisttree, 1, "COMMA", "a comma ','");
      verifyChildIsRule(termlisttree, 2, "termlist", "a list of terms");
      termlisttree = termlisttree.getChild(2);
    }
  }

  /**
   * This determines the FunctionSymbol associated with the given parse tree (which should be an
   * IDENTIFIER), provided that it occurs in a context with numberOfArguments arguments.
   * If we are considering an mstrs, the symbol MUST be declared in the parsing data; if this is
   * not the case, a ParserException is thrown. If we are considering an unsorted trs, a function
   * symbol with a type given by the arity (and using only unit types) is declared and returned.
   */
  private FunctionSymbol readFunctionSymbol(ParseTree tree, ParseData data, int numberOfArguments,
                                            boolean mstrs) throws ParserException {
    String name = tree.getText();
    FunctionSymbol f = data.lookupFunctionSymbol(name);

    // It's declared!
    if (f != null) {
      if (f.queryType().queryArity() != numberOfArguments) {
        throw new TypingException(firstToken(tree), name, f.queryType().toString(),
                                  "type with arity " + numberOfArguments);
      }
      return f;
    }

    // declared as a variable?!?
    if (data.lookupVariable(name) != null) {
      throw new ParserException(firstToken(tree),
                                "Declared variable " + name + " used as function!");
    }

    // Not declared, but it really should be.
    if (mstrs) {
      throw new DeclarationException(firstToken(tree), name);
    }

    // Otherwise, create the type for the given arity and use it to construct a function symbol
    Type type = unitSort;
    for (int i = 0; i < numberOfArguments; i++) type = new ArrowType(unitSort, type);
    FunctionSymbol ret = new UserDefinedSymbol(name, type);
    data.addFunctionSymbol(ret);
    return ret;
  }

  /**
   * This reads the given term from the parse tree, and throws a parser exception if for example
   * typing does not check out.
   * If we are parsing a mstrs, then all unknown symbols are expected to be variables; if it is an
   * unsorted trs, then all unknown symbols are expected to be function symbols.
   */
  private Term readTerm(ParseTree tree, ParseData data, Type expectedType, boolean mstrs)
                                                                          throws ParserException {
    // sanity check: this input reader only reads terms of base type!
    if (expectedType != null && expectedType.queryTypeKind() != Type.TypeKind.BASETYPE) {
      throw buildError(tree, "Trying to read a term of non-basic type!");
    }
    verifyChildIsToken(tree, 0, "IDENTIFIER", "a function name or variable (an identifier)");

    // one child: a variable or constant function symbol
    if (tree.getChildCount() == 1) {
      return readConstantOrVariable(tree.getChild(0), data, expectedType, mstrs);
    }

    // otherwise: should be f() or f(<terms>)
    verifyChildIsToken(tree, 1, "BRACKETOPEN", "opening bracket '('");
    verifyChildIsToken(tree, tree.getChildCount()-1, "BRACKETCLOSE", "closing bracket ')'");

    // separate out all arguments
    ArrayList<ParseTree> args = new ArrayList<ParseTree>();
    if (tree.getChildCount() > 3) readTermList(tree.getChild(2), args);

    // read the root symbol, and parse the arguments
    FunctionSymbol f = readFunctionSymbol(tree.getChild(0), data, args.size(), mstrs);
    Type type = f.queryType();
    ArrayList<Term> termargs = new ArrayList<Term>();
    for (int i = 0; i < args.size(); i++) {
      Type inp = type.queryArrowInputType();
      termargs.add(readTerm(args.get(i), data, inp, mstrs));
      type = type.queryArrowOutputType();
    }

    // create the resulting term, verify its type, and return
    Term ret = new FunctionalTerm(f, termargs);
    if (expectedType != null && !ret.queryType().equals(expectedType)) {
      throw new TypingException(firstToken(tree), ret.toString(), ret.queryType().toString(),
                                expectedType.toString());
    }
    return ret;
  }

  /** This function reads a trsrule from the given parse tree. */
  private Rule readRule(ParseTree tree, ParseData data, boolean mstrs) throws ParserException {
    verifyChildIsRule(tree, 0, "term", "a term");
    verifyChildIsToken(tree, 1, "ARROW", "an arrow '->'");
    verifyChildIsRule(tree, 2, "term", "a term");
    Term left = readTerm(tree.getChild(0), data, null, mstrs);
    Term right = readTerm(tree.getChild(2), data, left.queryType(), mstrs);
    try { return new FirstOrderRule(left, right); }
    catch (IllegalRuleError e) {
      throw new ParserException(firstToken(tree), e.queryProblem());
    }
  }

  /** This function reads a rule list (RULES...) into a list of rules. */
  private ArrayList<Rule> readRuleList(ParseTree tree, ParseData data, boolean mstrs)
                                                                        throws ParserException {
    verifyChildIsToken(tree, 0, "RULESDECSTART", "(RULES");
    verifyChildIsToken(tree, tree.getChildCount()-1, "BRACKETCLOSE", "closing bracket ')'");
    ArrayList<Rule> ret = new ArrayList<Rule>();
    for (int i = 1; i < tree.getChildCount()-1; i++) {
      // in a many-sorted TRS, variables are not declared, and we only need to persist a variable
      // within a rule; in a sorted TRS, variables are pre-declared (and all have the same sort),
      // so should not be reset
      if (mstrs) data.clearVariables();
      ret.add(readRule(tree.getChild(i), data, mstrs));
    }
    return ret;
  }

  /* ========== READ A WHOLE TRS ========== */

  private TRS readTRS(ParseTree tree) throws ParserException {
    ParseData data = new ParseData();
    boolean mstrs = false;
    int k = 0;
    String kind = checkChild(tree, k);
    if (kind.equals("rule varlist")) {
      handleVarList(tree.getChild(k), data);
      k++;
      kind = checkChild(tree, k);
    }
    if (kind.equals("rule siglist")) {
      handleSignature(tree.getChild(k), data);
      /* Note that it is actually allowed by the syntax of an unsorted TRS to provide a signature.
       * However, when this is done, ALL the function symbols are required to be declared.  In that
       * case, we can safely treat the input file as a many-sorted TRS (with only the unit sort).
       */
      mstrs = true;
      k++;
      kind = checkChild(tree, k);
    }
    verifyChildIsRule(tree, k, "ruleslist", "a list of rules");
    ArrayList<Rule> rules = readRuleList(tree.getChild(k), data, mstrs);
    return new TermRewritingSystem(data.queryCurrentAlphabet(), rules);
  }

  /* ========== STATIC ACCESS METHODS ========== */

  /** Note: public ONLY for use in unit testing; please use the static access methods otherwise. */
  public static TrsParser createTrsParserFromString(String str, ErrorCollector collector) {
    TrsLexer lexer = new TrsLexer(CharStreams.fromString(str));
    lexer.removeErrorListeners();
    lexer.addErrorListener(collector);
    TrsParser parser = new TrsParser(new CommonTokenStream(lexer));
    parser.removeErrorListeners();
    parser.addErrorListener(collector);
    return parser;
  }

  /** Sets up a (lexer and) parser from the given file, using the given error collector. */
  private static TrsParser createTrsParserFromFile(String filename, ErrorCollector collector)
                                                                               throws IOException {
    ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(filename));
    TrsLexer lexer = new TrsLexer(input);
    lexer.removeErrorListeners();
    lexer.addErrorListener(collector);
    TrsParser parser = new TrsParser(new CommonTokenStream(lexer));
    parser.removeErrorListeners();
    parser.addErrorListener(collector);
    return parser;
  }

  /**
   * Reads an unsorted first-order term from the input and returns it; vars are the declared
   * variables.
   */
  public static Term readUnsortedTermFromString(String str, ArrayList<String> varnames)
                                                                      throws ParserException {
    ErrorCollector collector = new ErrorCollector();
    TrsParser parser = createTrsParserFromString(str, collector);
    TrsInputReader reader = new TrsInputReader();
    ParseTree tree = parser.term();
    collector.throwCollectedExceptions();

    ParseData data = new ParseData();
    for (int i = 0; i < varnames.size(); i++) {
      data.addVariable(new Var(varnames.get(i), unitSort));
    }
    return reader.readTerm(tree, data, unitSort, false);
  }

  /**
   * Reads a many-sorted first-order term from the input and returns it; the TRS should give types
   * for ALL the function symbols occurring in the input.
   * Note that this can safely be used for a TRS that was read as an unsorted TRS, since the
   * resulting TRS is always many-sorted (just with a single sort).
   */
  public static Term readTermFromString(String str, TRS trs) throws ParserException {
    ErrorCollector collector = new ErrorCollector();
    TrsParser parser = createTrsParserFromString(str, collector);
    TrsInputReader reader = new TrsInputReader();
    ParseTree tree = parser.term();
    collector.throwCollectedExceptions();

    ParseData data = new ParseData(trs);
    return reader.readTerm(tree, data, null, true);
  }

  /** Parses the given program, and returns the TRS that it defines. */
  public static TRS readTrsFromString(String str) throws ParserException {
    ErrorCollector collector = new ErrorCollector();
    TrsParser parser = createTrsParserFromString(str, collector);
    TrsInputReader reader = new TrsInputReader();
    ParseTree tree = parser.trs();
    collector.throwCollectedExceptions();

    return reader.readTRS(tree);
  }

  /** Reads the given file, parses the program in it, and returns the TRS that it defines. */
  public static TRS readTrsFromFile(String filename) throws ParserException, IOException {
    ErrorCollector collector = new ErrorCollector();
    TrsParser parser = createTrsParserFromFile(filename, collector);
    TrsInputReader reader = new TrsInputReader();
    ParseTree tree = parser.trs();
    collector.throwCollectedExceptions();

    return reader.readTRS(tree);
  }
}

