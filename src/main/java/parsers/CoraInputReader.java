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

import cora.exceptions.ParserError;
import cora.exceptions.ParserException;
import cora.exceptions.DeclarationException;
import cora.exceptions.TypingException;
import cora.interfaces.types.Type;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Variable;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.rewriting.TRS;
import cora.types.*;
import cora.terms.*;
import cora.rewriting.*;

/**
 * This class reads text from string or file written in the Cora input format.
 * This is primarily intended to read input by the users, but may also be used internally to, for
 * instance, quickly construct a term (especially as part of unit testing).
 */
public class CoraInputReader extends InputReader {
  public CoraInputReader() {
    super(CoraParser.VOCABULARY, CoraParser.ruleNames);
  }

  /* ========== BASICS (beyond those supplied by the inherit) ========== */

  /**
   * This function returns the relevant token text string if the given tree is
   * constant(STRING) or constant(IDENTIFIER).
   * If not, null is returned. However, if the tree has a form constant(<something else>) a
   * ParserError is thrown since this should not happen.
   */
  private String readConstant(ParseTree tree) {
    String rulename = getRuleName(tree);
    if (rulename == null || !rulename.equals("constant")) return null;
    if (tree.getChildCount() != 1) {
      throw buildError(tree, "constant tree has " + tree.getChildCount() + " children.");
    }
    String kind = checkChild(tree, 0);
    if ((kind.equals("token IDENTIFIER") || kind.equals("token STRING"))) {
      return tree.getText();
    }
    throw buildError(tree, "Child of constant is " + kind + "!");
  }

  /* ========== TYPE PARSING ========== */

  /** Turns the given tree, whose root rule must be "constant", into a Sort. */
  private Type readTypeConstant(ParseTree tree) {
    String constant = readConstant(tree);
    if (constant != null) return new Sort(constant);
    throw buildError(tree, "readTypeConstant called with a parsetree that is not constant.");
  }

  /** Turns the given tree, whose root rule must be "lowarrowtype", into a Type. */
  private Type readLowArrowType(ParseTree tree) {
    verifyChildIsRule(tree, 0, "constant", "a (string or identifier) constant");
    verifyChildIsToken(tree, 1, "ARROW", "type arrow (->)");
    verifyChildIsRule(tree, 2, "type", "a type");
    Type input = readTypeConstant(tree.getChild(0));
    Type output = readType(tree.getChild(2));
    return new ArrowType(input, output);
  }

  /** Turns the given tree, whose root rule must be "higherarrowtype", into a Type. */
  private Type readHigherArrowType(ParseTree tree) {
    verifyChildIsToken(tree, 0, "BRACKETOPEN", "opening bracket '('");
    verifyChildIsRule(tree, 1, "type", "input type");
    verifyChildIsToken(tree, 2, "BRACKETCLOSE", "closing bracket ')'");
    verifyChildIsToken(tree, 3, "ARROW", "type arrow (->)");
    verifyChildIsRule(tree, 4, "type", "output type");
    Type input = readType(tree.getChild(1));
    Type output = readType(tree.getChild(4));
    return new ArrowType(input, output);
  }
  
  /** Reads a Type from an Antlr ParseTree. */
  private Type readType(ParseTree tree) {
    String kind = checkChild(tree, 0);
    if (kind == null) throw buildError(tree, "Type has " + tree.getChildCount() + " children.");
    if (kind.equals("rule constant")) return readTypeConstant(tree.getChild(0));
    if (kind.equals("rule lowarrowtype")) return readLowArrowType(tree.getChild(0));
    if (kind.equals("rule higherarrowtype")) return readHigherArrowType(tree.getChild(0));
    throw buildError(tree, "Child of type has an unexpected shape (" + kind + ").");
  }

  /** Reads a "full type" (type followed by EOF) from the given parsetree. */
  private Type readFullType(ParseTree tree) {
    verifyChildIsRule(tree, 0, "type", "a type");
    verifyChildIsToken(tree, 1, "EOF", "end of input");
    return readType(tree.getChild(0));
  }

  /* ========== TERM PARSING ========== */

  /**
   * This function determines whether the given string is a valid variable.
   * Variables may consist only of letters, digits and the underscore, and must start with a letter
   * or underscore.
   */
  private boolean isValidVariable(String txt) {
    if (txt == null || txt.equals("")) return false;
    for (int i = 0; i < txt.length(); i++) {
      Character a = txt.charAt(i);
      if (!Character.isLetterOrDigit(a) && !a.equals('_')) return false;
    }
    return !Character.isDigit(txt.charAt(0));
  }

  /**
   * Given that tree wraps the given constant, and given that the given constant is not declard as
   * a function symbol, this function tries to parse it into a Variable, updating expectedType if
   * appropriate.
   */
  private Variable readVariable(ParseTree tree, String constant, ParseData pd,
                                       Type expectedType) throws ParserException {
    if (!isValidVariable(constant)) {
      throw new DeclarationException(firstToken(tree), constant, "not a valid variable");
    }
    // Variables do not need to be declared, but they must be used consistently; the same name
    // should always return tothe same variable. To this end, we save them in the parser data once
    // we're done
    Variable x = pd.lookupVariable(constant);
    if (x == null) {
      if (expectedType == null) {
        throw new DeclarationException(firstToken(tree), constant, "If this is a variable, " +
            "its type cannot be derived from context.");
      }
      x = new Var(constant, expectedType);
      pd.addVariable(x);
    }
    else if (expectedType != null && !x.queryType().equals(expectedType)) {
      throw new TypingException(firstToken(tree), constant, x.queryType().toString(),
                                expectedType.toString());
    }
    return x;
  }

  /**
   * Given that tree is a parse tree for a term of the form <function symbol> <bracket> <term>
   * <commatermlist>, this function reads the entire argument list into an arraylist. No term
   * parsing is yet done.
   */
  private ArrayList<ParseTree> readCommaSeparatedList(ParseTree tree) {
    ArrayList<ParseTree> ret = new ArrayList<ParseTree>();
    verifyChildIsToken(tree, 1, "BRACKETOPEN", "an opening bracket '('");
    verifyChildIsRule(tree, 2, "term", "a term");
    ret.add(tree.getChild(2));
    verifyChildIsRule(tree, 3, "commatermlist", "a comma-separated list of terms");
    ParseTree list = tree.getChild(3);
    while (true) {
      String kind = checkChild(list, 0);
      if (kind.equals("token BRACKETCLOSE")) return ret;
      verifyChildIsToken(list, 0, "COMMA", "comma ','");
      verifyChildIsRule(list, 1, "term", "a term");
      verifyChildIsRule(list, 2, "commatermlist", "a comma-separated list of terms");
      ret.add(list.getChild(1));
      list = list.getChild(2);
    }
  }

  /**
   * Reads the given parsetree (which is assumed to map to a "term" rule occurrence) into a term.
   * @see readTermFromString.
   */
  private Term readTerm(ParseTree tree, ParseData pd,
                               Type expectedType) throws ParserException {
    verifyChildIsRule(tree, 0, "constant", "a declared function symbol or variable");
    String constant = readConstant(tree.getChild(0));
    FunctionSymbol f = pd.lookupFunctionSymbol(constant);
    if (f == null) {
      if (tree.getChildCount() == 1) return readVariable(tree, constant, pd, expectedType);
      throw new DeclarationException(firstToken(tree), constant);
    }

    // find the (possibly empty) arguments list for this functional term
    ArrayList<ParseTree> arguments;
    if (tree.getChildCount() == 1 || checkChild(tree,2).equals("token BRACKETCLOSE")) {
      arguments = new ArrayList<ParseTree>();
    }
    else arguments = readCommaSeparatedList(tree);

    // parse the arguments and typecheck them against the input types of f
    ArrayList<Term> args = new ArrayList<Term>();
    Type type = f.queryType();
    for (int i = 0; i < arguments.size(); i++) {
      if (!type.isArrowType()) {
        throw new TypingException(firstToken(tree), constant, type.toString(),
                                  "type of arity at least " + arguments.size());
      }
      args.add(readTerm(arguments.get(i), pd, type.queryArrowInputType()));
      type = type.queryArrowOutputType();
    }
    
    // also typecheck the overall type of the term against the expected type
    if (expectedType != null && !type.equals(expectedType)) {
      throw new TypingException(firstToken(tree), tree.getText(), type.toString(),
                                expectedType.toString());
    }
    return new FunctionalTerm(f, args);
  }

  /**
   * Reads a term from the given parse tree, using ParseData for the declarations of function
   * symbols and variables.
   * Function symbols must be predeclared; variables do not need to be, as long as their type can
   * be derived from the input. These variable-type mappings are added into the parse data.
   * A parser exception is thrown if the given string cannot be (unambiguously) translated into a
   * term of the expected type. If expected = null, this final typecheck is omitted, but parsing
   * (and internal typechecking) may still fail for other reasons.
   */
  public Term readFullTerm(ParseTree tree, ParseData pd, Type expectedType) throws ParserException {
    verifyChildIsRule(tree, 0, "term", "a term");
    verifyChildIsToken(tree, 1, "EOF", "end of input");
    return readTerm(tree.getChild(0), pd, expectedType);
  }


  /* ========== WHOLE PROGRAM PARSING ========== */

  private Rule readRule(ParseTree tree, ParseData pd) throws ParserException {
    verifyChildIsRule(tree, 0, "term", "the left-hand side (a term)");
    verifyChildIsToken(tree, 1, "ARROW", "the rule arrow");
    verifyChildIsRule(tree, 2, "term", "the right-hand side (a term)");
    Term left = readTerm(tree.getChild(0), pd, null);
    Type type = left.queryType();
    Term right = readTerm(tree.getChild(2), pd, type);
    pd.clearVariables();
    return new SimpleRule(left, right);
  }

  /**
   * Given that the top of tree is a declaration, this function parses the declaration and adds it
   * to the parsing data.
   * If the declaration changes an existing declaration in pd, a parserexception is thrown.
   */
  private void updateDataForDeclaration(ParseTree tree,
                                               ParseData pd) throws ParserException {
    verifyChildIsRule(tree, 0, "constant", "a function symbol name (an identifier or string)");
    verifyChildIsToken(tree, 1, "DECLARE", "the declaration token ::");
    verifyChildIsRule(tree, 2, "type", "a type");
    String constant = readConstant(tree.getChild(0));
    Type type = readType(tree.getChild(2));
    FunctionSymbol declaring = new UserDefinedSymbol(constant, type);
    FunctionSymbol existing = pd.lookupFunctionSymbol(constant);
    if (existing == null) pd.addFunctionSymbol(declaring);
    else if (!declaring.equals(existing)) {
      throw new ParserException(firstToken(tree), "Redeclaration of " + constant +
        "; previously declared with type " + existing.queryType().toString());
    }
  }

  /**
   * Reads a program into the TRS it defines.  Here, it is assumed that the tree is a "program"
   * context.
   */
  private TRS readProgram(ParseTree tree) throws ParserException {
    ParseData pd = new ParseData();
    ArrayList<Rule> ret = new ArrayList<Rule>();

    while (tree.getChildCount() != 0) {
      verifyChildIsRule(tree, 1, "program", "a program");
      String kind = checkChild(tree, 0);
      if (kind.equals("rule simplerule")) ret.add(readRule(tree.getChild(0), pd));
      else if (kind.equals("rule declaration")) updateDataForDeclaration(tree.getChild(0), pd);
      else {
        throw buildError(tree, "Child of program is " + kind + "!");
      }
      tree = tree.getChild(1);
    }

    return new TermRewritingSystem(pd.queryCurrentAlphabet(), ret);
  }

  private TRS readFullProgram(ParseTree tree) throws ParserException {
    verifyChildIsRule(tree, 0, "program", "a program");
    verifyChildIsToken(tree, 1, "EOF", "end of input");
    return readProgram(tree.getChild(0));
  }

  /* ========== STATIC ACCESS METHODS ========== */

  /** Sets up a (lexer and) parser with the given error collector as listeners. */
  private static CoraParser createCoraParserFromString(String str, ErrorCollector collector) {
    CoraLexer lexer = new CoraLexer(CharStreams.fromString(str));
    lexer.removeErrorListeners();
    lexer.addErrorListener(collector);
    CoraParser parser = new CoraParser(new CommonTokenStream(lexer));
    parser.removeErrorListeners();
    parser.addErrorListener(collector);
    return parser;
  }

  /** Sets up a (lexer and) parser from the given file, using the given error collector. */
  private static CoraParser createCoraParserFromFile(String filename, ErrorCollector collector)
                                                                               throws IOException {
    ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(filename));
    CoraLexer lexer = new CoraLexer(input);
    lexer.removeErrorListeners();
    lexer.addErrorListener(collector);
    CoraParser parser = new CoraParser(new CommonTokenStream(lexer));
    parser.removeErrorListeners();
    parser.addErrorListener(collector);
    return parser;
  }


  /** Returns the Type represented by the given string. */
  public static Type readTypeFromString(String str) throws ParserException {
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createCoraParserFromString(str, collector);
    CoraInputReader reader = new CoraInputReader();
    ParseTree tree = parser.onlytype();
    collector.throwCollectedExceptions();

    return reader.readFullType(tree);
  }

  /**
   * Reads the given string into a term, using the given TRS to parse its function symbols.
   * The type is the expected type of the term, or null if no type is expected.
   */
  public static Term readTermFromString(String str, TRS trs, Type expectedType)
                                                          throws ParserException {
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createCoraParserFromString(str, collector);
    CoraInputReader reader = new CoraInputReader();
    ParseTree tree = parser.onlyterm();
    collector.throwCollectedExceptions();

    ParseData pd = new ParseData(trs);
    return reader.readFullTerm(tree, pd, expectedType);
  }

  /**
   * Reads the given string into a term, updating the given ParseData as it goes along.
   * This function is ONLY meant to be used for testing!
   */
  public static Term testReadTermFromString(String str, ParseData pd, Type expectedType)
                                                              throws ParserException {
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createCoraParserFromString(str, collector);
    CoraInputReader reader = new CoraInputReader();
    ParseTree tree = parser.onlyterm();
    collector.throwCollectedExceptions();
    return reader.readFullTerm(tree, pd, expectedType);
  }

  /**
   * Reads the given string into a term, using the given TRS to parse its function symbols.
   * This is supposed to only be called with *internal* input (for example from the unit testers),
   * where it is guaranteed that the string is well-formed and well-typed.
   * If any exceptions do occur, they are caught and passed on to a ParserError.
   */
  public static Term readTermFromString(String str, TRS trs) {
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createCoraParserFromString(str, collector);
    CoraInputReader reader = new CoraInputReader();
    ParseTree tree = parser.onlyterm();

    ParseData pd = new ParseData(trs);
    try {
      collector.throwCollectedExceptions();
      return reader.readFullTerm(tree, pd, null);
    }
    catch (ParserException e) {
      Token token = e.queryProblematicToken();
      throw new ParserError(token, token.toString(),
        "Parser exception on internally supplied string: " + e.getMessage());
    }
  }

  /** Parses the given program, and returns the TRS that it defines. */
  public static TRS readProgramFromString(String str) throws ParserException {
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createCoraParserFromString(str, collector);
    CoraInputReader reader = new CoraInputReader();
    ParseTree tree = parser.input();
    collector.throwCollectedExceptions();

    return reader.readFullProgram(tree);
  }

  /** Reads the given file, parses the program in it, and returns the TRS that it defines. */
  public static TRS readProgramFromFile(String filename) throws ParserException, IOException {
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createCoraParserFromFile(filename, collector);
    CoraInputReader reader = new CoraInputReader();
    ParseTree tree = parser.input();
    collector.throwCollectedExceptions();

    return reader.readFullProgram(tree);
  }
}

