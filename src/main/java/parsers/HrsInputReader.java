/**************************************************************************************************
 Copyright 2020 Cynthia Kop

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
import java.util.TreeMap;
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
import cora.terms.Constant;
import cora.terms.Var;
import cora.terms.BinderVariable;
import cora.terms.FunctionalTerm;
import cora.terms.Abstraction;
import cora.terms.Subst;
import cora.rewriting.FirstOrderRule;
import cora.rewriting.TermRewritingSystem;

/**
 * This class reads text from string or file written in the .hrs format from the international
 * confluence competition.
 */
public class HrsInputReader extends InputReader {
  public HrsInputReader() {
    super(HrsParser.VOCABULARY, HrsParser.ruleNames);
  }

  /* ========== TYPE PARSING ========== */

  /** Reads a Type from an Antlr ParseTree. */
  private Type readType(ParseTree tree) {
    String kind = checkChild(tree, 0); 
    if (kind == null) throw buildError(tree, "Type has " + tree.getChildCount() + " children.");
    if (kind.equals("token IDENTIFIER")) {
      if (tree.getChildCount() == 1) return new Sort(tree.getChild(0).getText());
      verifyChildIsToken(tree, 1, "ARROW", "type arrow (->)");
      verifyChildIsRule(tree, 2, "type", "a type");
      return new ArrowType(new Sort(tree.getChild(0).getText()), readType(tree.getChild(2)));
    }
    else {
      verifyChildIsToken(tree, 0, "BRACKETOPEN", "identifier or opening bracket '('");
      verifyChildIsRule(tree, 1, "type", "a type");
      verifyChildIsToken(tree, 2, "BRACKETCLOSE", "closing bracket ')'");
      if (tree.getChildCount() == 3) return readType(tree.getChild(1));
      verifyChildIsToken(tree, 3, "ARROW", "type arrow (->)");
      verifyChildIsRule(tree, 4, "type", "a type");
      return new ArrowType(readType(tree.getChild(1)), readType(tree.getChild(4)));
    }
  }

  /** Reads a "full type" (type followed by EOF) from the given parsetree. */
  private Type readFullType(ParseTree tree) {
    verifyChildIsRule(tree, 0, "type", "a type");
    verifyChildIsToken(tree, 1, "EOF", "end of input");
    return readType(tree.getChild(0));
  }

  /* ========== SIGNATURE PARSING ========== */

  /* Reads a sub-signature (variables or function symbols) from an Antlr ParseTree */
  private TreeMap<String,Type> readSig(ParseTree tree) throws ParserException {
    TreeMap<String,Type> ret = new TreeMap<String,Type>();
    while (tree.getChildCount() > 0) {
      verifyChildIsToken(tree, 0, "IDENTIFIER", "identifier");
      verifyChildIsToken(tree, 1, "DECLARE", "type declaration symbol (:)");
      verifyChildIsRule(tree, 2, "type", "a type");
      verifyChildIsRule(tree, 3, "sig", "the remainder of the signature");
      String text = tree.getChild(0).getText();
      Type type = readType(tree.getChild(2));
      if (ret.containsKey(text)) {
        throw new ParserException(firstToken(tree), "duplicate key: " + text);
      }
      ret.put(text, type);
      tree = tree.getChild(3);
    }
    return ret;
  }

  /* Reads the signature (variables and function symbols) from an Antlr ParseTree */
  private ParseData readSignature(ParseTree tree) throws ParserException {
    ParseData data = new ParseData();
    TreeMap<String,Type> varsig, funsig;
    String kind = checkChild(tree, 0); 
    if (kind.equals("token VARSDECSTART")) {
      verifyChildIsToken(tree, 0, "VARSDECSTART", "(VAR");
      verifyChildIsRule(tree, 1, "sig", "a variable signature");
      verifyChildIsToken(tree, 2, "BRACKETCLOSE", "closing bracket");
      verifyChildIsToken(tree, 3, "FUNSDECSTART", "(FUN");
      verifyChildIsRule(tree, 4, "sig", "a function signature");
      verifyChildIsToken(tree, 5, "BRACKETCLOSE", "closing bracket");
      varsig = readSig(tree.getChild(1));
      funsig = readSig(tree.getChild(4));
    }
    else {
      verifyChildIsToken(tree, 0, "FUNSDECSTART", "(FUN");
      verifyChildIsRule(tree, 1, "sig", "a function signature");
      verifyChildIsToken(tree, 2, "BRACKETCLOSE", "closing bracket");
      verifyChildIsToken(tree, 3, "VARSDECSTART", "(VAR");
      verifyChildIsRule(tree, 4, "sig", "a variable signature");
      verifyChildIsToken(tree, 5, "BRACKETCLOSE", "closing bracket");
      funsig = readSig(tree.getChild(1));
      varsig = readSig(tree.getChild(4));
    }

    for (String name : varsig.keySet()) {
      data.addVariable(new Var(name, varsig.get(name)));
    }
    for (String name : funsig.keySet()) {
      if (data.lookupVariable(name) != null) {
        throw new ParserException(firstToken(tree),
          "symbol " + name + " declared both as variable and function symbol!");
      }
      data.addFunctionSymbol(new Constant(name, funsig.get(name)));
    }
    return data;
  }

  /* ========== TERM PARSING ========== */

  /**
   * Finds the variable or function symbol with the given name in the parse data, if any.
   * Throws a ParserException if the given symbol is not declared.
   */
  private Term identifierToTerm(ParseTree identifier, ParseData pd) throws ParserException{
    String text = identifier.getText();
    Term ret = pd.lookupVariable(text);
    if (ret == null) ret = pd.lookupFunctionSymbol(text);
    if (ret == null) {
      throw new ParserException(firstToken(identifier), "unknown identifier: " + text);
    }
    return ret;
  }

  /**
   * This reads the given "basic term" (which is either a single term or a list of terms) into the
   * given list, using the parse data to identify functions and variables.
   */
  private void readBasicTermIntoList(ParseTree tree, ParseData pd, ArrayList<Term> arr)
                                                                            throws ParserException{
    String kind = checkChild(tree, 0);
    if (kind.equals("token IDENTIFIER")) arr.add(identifierToTerm(tree.getChild(0), pd));
    else {
      verifyChildIsToken(tree, 0, "BRACKETOPEN", "opening bracket");
      verifyChildIsRule(tree, 1, "termlist", "a comma-separated list of terms");
      verifyChildIsToken(tree, 2, "BRACKETCLOSE", "closing bracket");
      readTermListIntoList(tree.getChild(1), pd, arr);
    }
  }

  /** This reads a comma-separated terms list into the given arraylist. */
  private void readTermListIntoList(ParseTree tree, ParseData pd, ArrayList<Term> arr)
                                                                            throws ParserException{
    while (true) {
      verifyChildIsRule(tree, 0, "term", "a term");
      arr.add(readTerm(tree.getChild(0), pd));
      if (tree.getChildCount() == 1) return;
      verifyChildIsToken(tree, 1, "COMMA", "a comma");
      verifyChildIsRule(tree, 2, "termlist", "a comma-separated list of terms");
      tree = tree.getChild(2);
    }
  }

  /** This reads the parse tree for an abstraction into a term. */
  private Term readAbstraction(ParseTree tree, ParseData pd) throws ParserException {
    verifyChildIsToken(tree, 0, "LAMBDA", "lambda symbol \\");

    // check all binders are distinct variables, and map them to binder variables
    Subst subst = new Subst();
    int k = tree.getChildCount()-2;
    for (int i = 1; i < k; i++) {
      verifyChildIsToken(tree, i, "IDENTIFIER", "a variable");
      Variable x = pd.lookupVariable(tree.getChild(i).getText());
      if (x == null) {
        throw new ParserException(firstToken(tree), "unknown variable in binder: " +
          tree.getChild(i).getText());
      }
      if (!subst.extend(x, new BinderVariable(x.queryName(), x.queryType()))) {
        throw new ParserException(firstToken(tree), "duplicate binder variable: " + x.toString());
      }
    }

    verifyChildIsRule(tree, tree.getChildCount()-1, "term", "a term");
    verifyChildIsToken(tree, tree.getChildCount()-2, "DOT", "abstraction dot . ");
    Term subterm = readTerm(tree.getChild(tree.getChildCount()-1), pd);

    // create the abstraction
    Term ret = subterm.substitute(subst);
    for (int i = k - 1; i > 0; i--) {
      Variable x = subst.get(pd.lookupVariable(tree.getChild(i).getText())).queryVariable();
      ret = new Abstraction(x, ret);
    }

    return ret;
  }

  private Term readTerm(ParseTree tree, ParseData pd) throws ParserException {
    ArrayList<Term> parts = new ArrayList<Term>();

    for (int i = 0; i < tree.getChildCount(); i++) {
      String kind = checkChild(tree, i); 
      if (kind.equals("rule basicterm")) readBasicTermIntoList(tree.getChild(i), pd, parts);
      if (kind.equals("rule abstraction")) parts.add(readAbstraction(tree.getChild(i), pd));
    }
    
    // We put the application together in the only typable way: this handles the ambiguity inherent
    // in the format  by parsing an application a b c either as a(b(c)) or as a(b,c) depending on
    // types; while formally this leads to typing some erroneously constructed terms, it avoids the
    // ambiguity that x f(y) would be parsed differently from x f (y).
    int index = 0;
    while (index < parts.size()-1) {
      Term part = parts.get(index);
      Term next = parts.get(index+1);
      if (part.queryType().isArrowType() &&
          part.queryType().queryArrowInputType().equals(next.queryType())) {
        parts.set(index, part.apply(next));
        parts.remove(index+1);
        if (index > 0) index--;
      }
      else index++;
    }
    
    if (parts.size() == 1) return parts.get(0);

    String applstring = parts.get(0).toString();
    for (int i = 1; i < parts.size(); i++) applstring += "  " + parts.get(i).toString();
    throw new ParserException(firstToken(tree), "Typing exception on parsing " + tree.getText() +
      ": ill-typed application " + applstring + ".");
  }

  /** Reads a "full term" (term followed by EOF) from the given parsetree. */
  private Term readFullTerm(ParseTree tree, ParseData pd) throws ParserException {
    verifyChildIsRule(tree, 0, "term", "a type");
    verifyChildIsToken(tree, 1, "EOF", "end of input");
    return readTerm(tree.getChild(0), pd);
  }

  /* ========== STATIC ACCESS METHODS ========== */

  /** Sets up a parser from the given string, using the given error collector. */
  private static HrsParser createHrsParserFromString(String str, ErrorCollector collector) {
    HrsLexer lexer = new HrsLexer(CharStreams.fromString(str));
    lexer.removeErrorListeners();
    lexer.addErrorListener(collector);
    HrsParser parser = new HrsParser(new CommonTokenStream(lexer));
    parser.removeErrorListeners();
    parser.addErrorListener(collector);
    return parser;
  }

  /** Sets up a (lexer and) parser from the given file, using the given error collector. */
  private static HrsParser createHrsParserFromFile(String filename, ErrorCollector collector)
                                                                               throws IOException {
    ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(filename));
    HrsLexer lexer = new HrsLexer(input);
    lexer.removeErrorListeners();
    lexer.addErrorListener(collector);
    HrsParser parser = new HrsParser(new CommonTokenStream(lexer));
    parser.removeErrorListeners();
    parser.addErrorListener(collector);
    return parser;
  }

  /** Reads the given string into a type. */
  public static Type readTypeFromString(String str) throws ParserException {
    ErrorCollector collector = new ErrorCollector();
    HrsParser parser = createHrsParserFromString(str, collector);
    HrsInputReader reader = new HrsInputReader();
    ParseTree tree = parser.fulltype();
    collector.throwCollectedExceptions();
    return reader.readFullType(tree);
  }

  /** Reads the given signature into a ParseData.  Only to be used for testing. */
  public static ParseData readSignatureFromStringUT(String str) throws ParserException {
    ErrorCollector collector = new ErrorCollector();
    HrsParser parser = createHrsParserFromString(str, collector);
    HrsInputReader reader = new HrsInputReader();
    ParseTree tree = parser.signature();
    collector.throwCollectedExceptions();
    return reader.readSignature(tree);
  }

  /**
   * Reads the given string into a term, using the ParseData as reference for the types of function
   * symbols and variables occurring in it.
   * Note: all function symbols and variables in str are expected to be declared! If not, a
   * ParserException will be thrown.
   */
  public static Term readTermFromString(String str, ParseData pd) throws ParserException {
    ErrorCollector collector = new ErrorCollector();
    HrsParser parser = createHrsParserFromString(str, collector);
    HrsInputReader reader = new HrsInputReader();
    ParseTree tree = parser.fullterm();
    collector.throwCollectedExceptions();
    return reader.readFullTerm(tree, pd);
  }

}

