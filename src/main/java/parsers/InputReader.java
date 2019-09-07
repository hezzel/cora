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
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Vocabulary;

import cora.exceptions.ParserError;

/** This class provides shared functionality for all the input readers. */
abstract class InputReader {
  private Vocabulary _vocabulary;
  private String[] _ruleNames;

  public InputReader(Vocabulary vocab, String[] rulenames) {
    _vocabulary = vocab;
    _ruleNames = rulenames;
  }

  /** If the current tree is a terminal, returns its display name; otherwise returns null. */
  protected String getTerminalNodeName(ParseTree tree) {
    if (!(tree instanceof TerminalNode)) return null;
    Token token = ((TerminalNode)tree).getSymbol();
    return _vocabulary.getSymbolicName(token.getType());
  }

  /** If the current tree is a rule context, returns the corresponding rulename; otherwise null. */
  protected String getRuleName(ParseTree tree) {
    if (!(tree instanceof ParserRuleContext)) return null;
    ParserRuleContext cxt = (ParserRuleContext)tree;
    return _ruleNames[cxt.getRuleIndex()];
  }

  /** Gets the first Token of the given parse tree, for use in ParseExceptions and ParseErrors. */
  protected Token firstToken(ParseTree tree) {
    if (tree instanceof TerminalNode) return ((TerminalNode)tree).getSymbol();
    if (tree instanceof ParserRuleContext) return ((ParserRuleContext)tree).getStart();
    return null;
  }

  /** Builds an Error to indicate that there is a problem with the given parse tree. */
  protected ParserError buildError(ParseTree tree, String message) {
    Token start = firstToken(tree);
    String text = tree.getText();
    if (start != null) return new ParserError(start, text, message);
    return new ParserError(0, 0, text,
                           message + " [Also: parse tree does not include any tokens.]");
  }

  /** This returns a description (including "token" or "rule") of the given child of tree. */
  protected String checkChild(ParseTree tree, int childindex) {
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
  protected void verifyChildIsRule(ParseTree tree, int childindex, String rulename, String desc) {
    String actual = checkChild(tree, childindex);
    if (!actual.equals("rule " + rulename)) {
      throw buildError(tree, "encountered " + actual + "; expected " + desc + ".");
    }
  }

  /**
   * This function checks that the given child of tree is a token with the given name.
   * If that is not the case, then a ParserError is thrown.
   */
  protected void verifyChildIsToken(ParseTree tree, int childindex, String tokenname, String desc) {
    String actual = checkChild(tree, childindex);
    if (!actual.equals("token " + tokenname)) {
      throw buildError(tree, "encountered " + actual + "; expected " + desc + ".");
    }
  }
}

