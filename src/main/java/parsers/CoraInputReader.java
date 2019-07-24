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

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.ParserRuleContext;
import cora.exceptions.ParserError;
import cora.exceptions.ParserException;
import cora.interfaces.types.Type;
import cora.immutabledata.types.*;

/**
 * This class reads text from string or file written in the Cora input format.
 * This is primarily intended to read input by the users, but may also be used internally to, for
 * instance, quickly construct a term (especially as part of unit testing).
 */
public class CoraInputReader {
  /** If the current tree is a terminal, returns its display name; otherwise returns null. */
  private static String getTerminalNodeName(ParseTree tree) {
    if (!(tree instanceof TerminalNode)) return null;
    Token token = ((TerminalNode)tree).getSymbol();
    return CoraParser.VOCABULARY.getSymbolicName(token.getType());
  }

  /** If the current tree is a rule context, returns the corresponding rulename; otherwise null. */
  private static String getRuleName(ParseTree tree) {
    if (!(tree instanceof ParserRuleContext)) return null;
    ParserRuleContext cxt = (ParserRuleContext)tree;
    return CoraParser.ruleNames[cxt.getRuleIndex()];
  }

  /** Gets the first Token of the given parse tree, for use in ParseExceptions and ParseErrors. */
  private static Token firstToken(ParseTree tree) {
    if (tree instanceof TerminalNode) return ((TerminalNode)tree).getSymbol();
    if (tree instanceof ParserRuleContext) return ((ParserRuleContext)tree).getStart();
    return null;
  }

  /** Builds an Error to indicate that there is a problem with the given parse tree. */
  private static ParserError buildError(ParseTree tree, String message) {
    Token start = firstToken(tree);
    String text = tree.getText();
    if (start != null) return new ParserError(start, text, message);
    return new ParserError(0, 0, text,
                           message + " [Also: parse tree does not include any tokens.]");
  }

  /** This returns a description (including "token" or "rule" of the given child of tree. */
  private static String checkChild(ParseTree tree, int childindex) {
    int childcount = tree.getChildCount();
    if (childcount <= childindex) return "<empty>";
    ParseTree child = tree.getChild(childindex);
    if (child == null) return "<null>";
    String ret = getTerminalNodeName(child);
    if (ret != null) return "token " + ret;
    ret = getRuleName(child);
    if (ret != null) return "rule " + ret;
    return "unexpected tree [" + child.getText() + "]";
  }

  /**
   * This function checks that the given child of tree is a rule with the given name.
   * If that is not the case, then a ParserError is thrown.
   */
  private static void verifyChildIsRule(ParseTree tree, int childindex, String rulename,
                                        String description) {
    String actual = checkChild(tree, childindex);
    if (!actual.equals("rule " + rulename)) {
      throw buildError(tree, "encountered " + actual + "; expected " + description + ".");
    }
  }

  /**
   * This function checks that the given child of tree is a token with the given name.
   * If that is not the case, then a ParserError is thrown.
   */
  private static void verifyChildIsToken(ParseTree tree, int childindex, String tokenname,
                                         String description) {
    String actual = checkChild(tree, childindex);
    if (!actual.equals("token " + tokenname)) {
      throw buildError(tree, "encountered " + actual + "; expected " + description + ".");
    }
  }

  /**
   * This function returns the relevant token text string if the given tree is
   * constant(STRING) or constant(IDENTIFIER).
   * If not, null is returned. However, if the tree has a form constant(<something else>) a
   * ParserError is thrown since this should not happen.
   */
  private static String readConstant(ParseTree tree) {
    if (!(tree instanceof ParserRuleContext)) return null;
    String rulename = CoraParser.ruleNames[((ParserRuleContext)tree).getRuleIndex()];
    if (!rulename.equals("constant")) return null;
    if (tree.getChildCount() != 1) {
      throw buildError(tree, "constant tree has " + tree.getChildCount() + " children.");
    }
    ParseTree child = tree.getChild(0);
    String kind = getTerminalNodeName(child);
    if (kind != null && (kind.equals("IDENTIFIER") || kind.equals("STRING"))) {
      return ((TerminalNode)child).getSymbol().getText();
    }
    kind = getRuleName(child);
    if (kind == null) kind = "an unknown tree";
    throw buildError(tree, "Child of constant is " + kind + "!");
  }

  /* ========== TYPE PARSING ========== */

  /** Turns the given tree, whose root rule must be "constant", into a Sort. */
  private static Type readTypeConstant(ParseTree tree) {
    String constant = readConstant(tree);
    if (constant != null) return new Sort(constant);
    throw buildError(tree, "readTypeConstant called with a parsetree that is not constant.");
  }

  /** Turns the given tree, whose root rule must be "lowarrowtype", into a Type. */
  private static Type readLowArrowType(ParseTree tree) {
    verifyChildIsRule(tree, 0, "constant", "a (string or identifier) constant");
    verifyChildIsToken(tree, 1, "ARROW", "type arrow (->)");
    verifyChildIsRule(tree, 2, "type", "a type");
    Type input = readTypeConstant(tree.getChild(0));
    Type output = readType(tree.getChild(2));
    return new ArrowType(input, output);
  }

  /** Turns the given tree, whose root rule must be "higherarrowtype", into a Type. */
  private static Type readHigherArrowType(ParseTree tree) {
    verifyChildIsToken(tree, 0, "BRACKETOPEN", "opening bracket '('");
    verifyChildIsRule(tree, 1, "type", "input type");
    verifyChildIsToken(tree, 2, "BRACKETCLOSE", "closing bracket '('");
    verifyChildIsToken(tree, 3, "ARROW", "type arrow (->)");
    verifyChildIsRule(tree, 4, "type", "output type");
    Type input = readType(tree.getChild(1));
    Type output = readType(tree.getChild(4));
    return new ArrowType(input, output);
  }
  
  /** Reads a Type from an Antlr ParseTree. */
  private static Type readType(ParseTree tree) {
    String kind = checkChild(tree, 0);
    if (kind == null) throw buildError(tree, "Type has " + tree.getChildCount() + " children.");
    if (kind.equals("rule constant")) return readTypeConstant(tree.getChild(0));
    if (kind.equals("rule lowarrowtype")) return readLowArrowType(tree.getChild(0));
    if (kind.equals("rule higherarrowtype")) return readHigherArrowType(tree.getChild(0));
    throw buildError(tree, "Child of type has an unexpected shape (" + kind + ").");
  }

  /** Sets up a (lexer and) parser with the given error collector as listeners. */
  private static CoraParser createCoraParser(String str, ErrorCollector collector) {
    CoraLexer lexer = new CoraLexer(CharStreams.fromString(str));
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
    CoraParser parser = createCoraParser(str, collector);
    ParseTree tree = parser.onlytype();
    collector.throwCollectedExceptions();
    verifyChildIsRule(tree, 0, "type", "a type");
    verifyChildIsToken(tree, 1, "EOF", "end of input");
    return readType(tree.getChild(0));
  }
}

