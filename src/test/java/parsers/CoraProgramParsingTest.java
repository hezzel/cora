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
import cora.exceptions.ParserException;
import cora.exceptions.AntlrParserException;

/** This class tests the antlr code for parsing types. */
public class CoraProgramParsingTest extends CoraParsingTestInherit {
  @Test
  public void testShortProgram() {
    String str = "f :: a -> a -> a b :: b f(x,x) -> x b -> b c :: a";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.input();
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(describeTop(tree).equals("input"));
    assertTrue(describeTop(tree.getChild(0)).equals("program"));
    tree = tree.getChild(0);
    assertTrue(describeTop(tree.getChild(0)).equals("declaration"));
    tree = tree.getChild(1);
    assertTrue(describeTop(tree.getChild(0)).equals("declaration"));
    tree = tree.getChild(1);
    assertTrue(describeTop(tree.getChild(0)).equals("simplerule"));
    tree = tree.getChild(1);
    assertTrue(describeTop(tree.getChild(0)).equals("simplerule"));
    tree = tree.getChild(1);
    assertTrue(describeTop(tree.getChild(0)).equals("declaration"));
    tree = tree.getChild(1);
    assertTrue(tree.getChildCount() == 0);
  }

  @Test
  public void testDeclaration() {
    String str = "f :: a -> a -> b :: c d :: e";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.input();
    assertTrue(collector.queryErrorCount() == 1);
  }

  @Test
  public void testRules() {
    String str = "f(x) -> g(2,x) a :: 3 g(a,y) -> a -> y";
    ErrorCollector collector = new ErrorCollector();
    CoraParser parser = createParser(str, collector);
    ParseTree tree = parser.input();
    assertTrue(collector.queryErrorCount() >= 1);
  }
}

