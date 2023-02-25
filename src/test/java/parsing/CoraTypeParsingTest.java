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

import org.junit.Test;
import static org.junit.Assert.*;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;
import java.util.ArrayList;

/** This class tests the antlr code for parsing types. */

public class CoraTypeParsingTest extends CoraParsingTestInherit {
  @Test
  public void testBaseType() {
    String str = "aKKaO";
    String expected = "onlytype(type(constant(IDENTIFIER(aKKaO))),EOF)";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlytype();
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(toStringParseTree(tree).equals(expected));
  }

  @Test
  public void testArrowType() {
    String str = "xx => yy";
    String expected = "onlytype(type(lowarrowtype(constant(IDENTIFIER(xx))," +
                        "typearrow(TYPEARROW),type(constant(IDENTIFIER(yy))))),EOF)";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlytype();
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(toStringParseTree(tree).equals(expected));
  }

  @Test
  public void testRightAssociativeType() {
    String str = "xx -> yy → zz";
    String expected = "onlytype(type(lowarrowtype(constant(IDENTIFIER(xx))," +
                        "typearrow(ARROW),type(lowarrowtype(constant(IDENTIFIER(yy))," +
                        "typearrow(ARROW),type(constant(IDENTIFIER(zz))))))),EOF)";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlytype();
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(toStringParseTree(tree).equals(expected));
  }

  @Test
  public void testHigherArrowType() {
    String str = "(xx => yy) ⇒ zz";
    String expected = "onlytype(type(higherarrowtype(BRACKETOPEN,type(" +
                        "lowarrowtype(constant(IDENTIFIER(xx)),typearrow(TYPEARROW),type(" +
                        "constant(IDENTIFIER(yy))))),BRACKETCLOSE,typearrow(TYPEARROW),type(" +
                        "constant(IDENTIFIER(zz))))),EOF)";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlytype();
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(toStringParseTree(tree).equals(expected));
  }

  @Test
  public void testUnnecessaryHigherType() {
    String str = "(a) -> b";
    String expected = "onlytype(type(higherarrowtype(BRACKETOPEN,type(" +
                        "constant(IDENTIFIER(a))),BRACKETCLOSE,typearrow(ARROW),type(" +
                        "constant(IDENTIFIER(b))))),EOF)";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlytype();
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(toStringParseTree(tree).equals(expected));
  }

  @Test
  public void testCombinedType() {
    String str = "a => (b → cd) -> e";
    String expected = "onlytype(" +
                        "type(lowarrowtype(constant(IDENTIFIER(a)),typearrow(TYPEARROW)," +
                          "type(higherarrowtype(BRACKETOPEN," +
                            "type(lowarrowtype(constant(IDENTIFIER(b)),typearrow(ARROW)," +
                            "type(constant(IDENTIFIER(cd)))))," +
                          "BRACKETCLOSE,typearrow(ARROW),type(constant(IDENTIFIER(e)))))))," +
                        "EOF)";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlytype();
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(toStringParseTree(tree).equals(expected));
  }

  @Test
  public void testTypeMissingArrow() {
    String str = "a b";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlytype();
    assertTrue(collector.queryErrorCount() == 1);
  }

  @Test
  public void testTypeMissingInput() {
    String str = "-> b";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlytype();
    assertTrue(collector.queryErrorCount() == 1);
  }

  @Test
  public void testTypeMissingOutput() {
    String str = "b ->";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlytype();
    assertTrue(collector.queryErrorCount() == 1);
  }

  @Test
  public void testMultipleTypeErrors() {
    String str = "x -> ((a -> b c) ->) ->";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.onlytype();
    assertTrue(collector.queryErrorCount() >= 1);
  }
}

