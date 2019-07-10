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
import cora.exceptions.ParserException;
import cora.interfaces.types.Type;
import cora.immutabledata.types.*;

/**
 * This class reads text from string or file written in the Cora input format.
 * This is primarily intended to read input by the users, but may also be used internally to, for
 * instance, quickly construct a term (especially as part of unit testing).
 */
public class CoraInputReader {
  /** Throws an exception to indicate that the given parse tree does not have the expected form. */
  private static Type throwParserException(ParseTree tree, String encountered,
                                           String expected) throws ParserException {
    // we need the first token of the tree to get the line and position for the exception
    if (tree instanceof TerminalNode) {
      Token token = ((TerminalNode)tree).getSymbol();
      throw new ParserException(token, encountered, expected);
    }
    if (tree instanceof ParserRuleContext) {
      ParserRuleContext cxt = (ParserRuleContext)tree;
      Token token = cxt.getStart();
      if (token != null) throw new ParserException(token, encountered, expected);
      String rulename = CoraParser.ruleNames[cxt.getRuleIndex()];
      throw new ParserException(0, 0, "Empty rule occurrence " + rulename + " at unknown " +
                                "position; encountered '" + encountered + "', expected '" +
                                expected + "'.");
    }
    throw new ParserException(0, 0, "Unexpected kind of parsetree at unknown position.");
  }


  /**
   * Turns the given node into a Sort if it is an identifier or string;
   * if not, throws a ParserException.
   */
  private static Type readSort(TerminalNode node) throws ParserException {
    Token token = node.getSymbol();
    String text = token.getText();
    int type = token.getType();
    if (type == CoraParser.STRING || type == CoraParser.IDENTIFIER) return new Sort(text);
    else {
      return throwParserException(node, CoraLexer.tokenNames[token.getType()],
                                       "identifier or string (to represent a sort)");
    }
  }
  
  /** Reads a Type from an Antlr ParseTree. */
  private static Type readType(ParseTree tree) throws ParserException {
    if (tree instanceof TerminalNode) return readSort((TerminalNode)tree);
    if (tree instanceof ParserRuleContext) {
      String rulename = CoraParser.ruleNames[((ParserRuleContext)tree).getRuleIndex()];
      if (rulename.equals("constant")) return readConstantType(tree);
      if (rulename.equals("type")) return readArrowType(tree);
      return throwParserException(tree, rulename, "arrow type or sort constant");
    }
    return throwParserException(tree, "unknown tree", "type");
  }

  private static Type readConstantType(ParseTree tree) throws ParserException {
    int childcount = tree.getChildCount();
    if (childcount != 1) throwParserException(tree, "constant with " + childcount + " children",
                                                    "one child");
    return readType(tree.getChild(0));
  }

  private static Type readArrowType(ParseTree tree) throws ParserException {
    int childcount = tree.getChildCount();
    if (childcount == 1) return readType(tree.getChild(0));
    if (childcount == 3) {
      return new ArrowType(readType(tree.getChild(0)), readType(tree.getChild(2)));
    }
    if (childcount == 5) {
      return new ArrowType(readType(tree.getChild(1)), readType(tree.getChild(4)));
    }
    return throwParserException(tree, "arrow type tree with " + childcount + " children",
                                      "1, 3 or 5 children");
  }

  /** Returns the Type represented by the given string. */
  public static Type readTypeFromString(String str) throws ParserException {
    CoraLexer lexer = new CoraLexer(CharStreams.fromString(str));
    CoraParser parser = new CoraParser(new CommonTokenStream(lexer));
    return readType(parser.type());
  }
}

