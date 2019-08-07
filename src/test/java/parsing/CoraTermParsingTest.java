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

import org.junit.Test;
import static org.junit.Assert.*;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.antlr.v4.runtime.tree.ParseTreeWalker;
import java.util.ArrayList;
import cora.parsers.CoraLexer;
import cora.parsers.CoraParser;
import cora.parsers.CoraParserBaseListener;
import cora.parsers.ErrorCollector;

/** This class tests the antlr code for parsing types. */

public class CoraTermParsingTest extends CoraParsingTestInherit {
  @Test
  public void testConstant() {
    String str = "aKKaO";
    String expected = "onlyterm(term(constant(IDENTIFIER(aKKaO))),EOF)";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlyterm();
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(toStringParseTree(tree).equals(expected));
  }

  @Test
  public void testEmptyFunctionApplication() {
    String str = "xx()";
    String expected = "onlyterm(term(constant(IDENTIFIER(xx)),BRACKETOPEN,BRACKETCLOSE),EOF)";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlyterm();
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(toStringParseTree(tree).equals(expected));
  }

  @Test
  public void testUnitaryFunctionApplication() {
    String str = "xx(a)";
    String expected = "onlyterm(term(constant(IDENTIFIER(xx)),BRACKETOPEN,term(constant(" +
                        "IDENTIFIER(a))),commatermlist(BRACKETCLOSE)),EOF)";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlyterm();
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(toStringParseTree(tree).equals(expected));
  }

  @Test
  public void testTripleFunctionApplication() {
    String str = "xx(a,b, cc)";
    String expected = "onlyterm(term(constant(IDENTIFIER(xx)),BRACKETOPEN,term(constant(" +
                        "IDENTIFIER(a))),commatermlist(COMMA,term(constant(IDENTIFIER(b)))," +
                        "commatermlist(COMMA,term(constant(IDENTIFIER(cc)))," +
                        "commatermlist(BRACKETCLOSE)))),EOF)";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlyterm();
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(toStringParseTree(tree).equals(expected));
  }

  @Test
  public void testNestedFunctionApplication() {
    String str = "xx(a, b(\"cc\", \"d\"()), e)";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlyterm();
    assertEquals(describeTop(tree), "onlyterm");
    assertTrue(tree.getChildCount() == 2);
    tree = tree.getChild(0);
    assertEquals(describeTop(tree), "term");
    assertTrue(tree.getChildCount() == 4);
    assertEquals(toStringParseTree(tree.getChild(0)), "constant(IDENTIFIER(xx))");
    assertEquals(toStringParseTree(tree.getChild(2)), "term(constant(IDENTIFIER(a)))");
    tree = tree.getChild(3);
    assertEquals(describeTop(tree), "commatermlist");
    assertTrue(tree.getChildCount() == 3);
    ParseTree bccd = tree.getChild(1);
    tree = tree.getChild(2);
    assertEquals(describeTop(tree), "commatermlist");
    assertTrue(tree.getChildCount() == 3);
    assertEquals(toStringParseTree(tree.getChild(1)), "term(constant(IDENTIFIER(e)))");
    assertEquals(toStringParseTree(tree.getChild(2)), "commatermlist(BRACKETCLOSE)");
    assertEquals(describeTop(bccd), "term");
    tree = bccd;
    assertTrue(tree.getChildCount() == 4);
    assertEquals(toStringParseTree(tree.getChild(0)), "constant(IDENTIFIER(b))");
    assertEquals(toStringParseTree(tree.getChild(2)), "term(constant(STRING(cc)))");
    tree = tree.getChild(3);
    assertEquals(describeTop(tree), "commatermlist");
    assertTrue(tree.getChildCount() == 3);
    assertEquals(toStringParseTree(tree.getChild(2)), "commatermlist(BRACKETCLOSE)");
    tree = tree.getChild(1);
    assertEquals(describeTop(tree), "term");
    assertTrue(tree.getChildCount() == 3);
    assertEquals(toStringParseTree(tree.getChild(0)), "constant(STRING(d))");
  }

  @Test
  public void testTermMissingBracket() {
    String str = "f(a,b";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlyterm();
    assertTrue(collector.queryErrorCount() == 1);
  }

  @Test
  public void testTermInfix() {
    String str = "a o b";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlyterm();
    assertTrue(collector.queryErrorCount() >= 1);
  }
}

