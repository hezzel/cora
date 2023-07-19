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

package cora.parsing;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.exceptions.ParseError;
import cora.types.Type;
import cora.types.TypeFactory;
import cora.terms.Term;
import cora.terms.Variable;
import cora.terms.FunctionSymbol;
import cora.terms.TermFactory;
import cora.rewriting.Rule;
import cora.rewriting.TRS;
import cora.parsing.lib.ErrorCollector;
import cora.parsing.lib.ParsingStatus;

public class CoraInputReaderTypeTest {
  private ParsingStatus makeStatus(String text) {
    return new ParsingStatus(CoraTokenData.getStringLexer(text), 10);
  }

  private ParsingStatus makeStatus(String text, ErrorCollector collector) {
    return new ParsingStatus(CoraTokenData.getStringLexer(text), collector);
  }

  @Test
  public void testReadConstantBaseType() {
    Type t = CoraInputReader.readTypeFromString("aKKaO");
    assertTrue(t.isBaseType());
    assertTrue(t.toString().equals("aKKaO"));
  }

  @Test
  public void testReadStringBaseType() {
    Type t = CoraInputReader.readTypeFromString("\"hello\" \" world\"");
    assertTrue(t.isBaseType());
    assertTrue(t.toString().equals("hello world"));
  }

  @Test
  public void testSimpleArrowType() {
    Type t = CoraInputReader.readTypeFromString("xx ⇒ yy");
    assertTrue(t.isArrowType());
    assertTrue(t.queryArrowInputType().toString().equals("xx"));
    assertTrue(t.queryArrowOutputType().toString().equals("yy"));
  }

  @Test
  public void testSimpleArrowTypeWithPlainArrow() {
    Type t = CoraInputReader.readTypeFromString("xx -> yy");
    assertTrue(t.isArrowType());
    assertTrue(t.queryArrowInputType().toString().equals("xx"));
    assertTrue(t.queryArrowOutputType().toString().equals("yy"));
  }

  @Test
  public void testRightAssociativeType() {
    Type t = CoraInputReader.readTypeFromString("xx -> yy ⇒ zz");
    assertTrue(t.isArrowType());
    assertTrue(t.queryArrowInputType().toString().equals("xx"));
    assertTrue(t.queryArrowOutputType().isArrowType());
    assertTrue(t.queryArrowOutputType().toString().equals("yy ⇒ zz"));
  }

  @Test
  public void testHigherArrowType() {
    Type t = CoraInputReader.readTypeFromString("(xx -> yy) -> zz");
    assertTrue(t.isArrowType());
    assertTrue(t.queryArrowInputType().isArrowType());
    assertTrue(t.queryArrowInputType().toString().equals("xx ⇒ yy"));
    assertTrue(t.queryArrowOutputType().toString().equals("zz"));
  }

  @Test
  public void testUnnecessaryHigherType() {
    Type t = CoraInputReader.readTypeFromString("(a) -> b");
    assertTrue(t.isArrowType());
    assertTrue(t.queryArrowInputType().toString().equals("a"));
    assertTrue(t.queryArrowOutputType().toString().equals("b"));
  }

  @Test
  public void testReadTypeWithBracketsInTheMiddle() {
    Type t = CoraInputReader.readTypeFromString("a -> (b -> cd) -> e");
    assertTrue(t.isArrowType());
    assertTrue(t.toString().equals("a ⇒ (b ⇒ cd) ⇒ e"));
  }

  @Test
  public void testReadTypeEndingWithBrackets() {
    Type t = CoraInputReader.readTypeFromString("(a -> b) ⇒ (c -> d ⇒ e)");
    assertTrue(t.isArrowType());
    assertTrue(t.queryArrowInputType().toString().equals("a ⇒ b"));
    assertTrue(t.queryArrowOutputType().toString().equals("c ⇒ d ⇒ e"));
  }

  @Test(expected = ParseError.class)
  public void testArrowTypeWithIncorrectArrow() {
    Type t = CoraInputReader.readTypeFromString("xx → yy");
  }

  @Test
  public void testArrowTypeWithIncorrectArrowRecovery() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("xx → yy zz", collector);
    Type t = CoraInputReader.readTypeForUnitTest(status);
    assertTrue(t.toString().equals("xx ⇒ yy"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:4: Rule arrow → occurs in a type; did you mean ⇒?\n"));
  }

  @Test
  public void testReadTypeWithDoubleArrowRecovery() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("a -> b -> -> c", collector);
    Type t = CoraInputReader.readTypeForUnitTest(status);
    assertTrue(t.toString().equals("a ⇒ b ⇒ c"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:11: Expected a type (started by a constant or bracket) but got ARROW (->).\n"));
  }

  @Test(expected = ParseError.class)
  public void testArrowTypeWithNonExistingArrowWhileFullTypeIsRequested() {
    Type t = CoraInputReader.readTypeFromString("xx => yy");
    assertTrue(t.toString().equals("xx"));
  }

  @Test
  public void testArrowTypeWithNonExistingArrow() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("xx => yy", collector);
    Type t = CoraInputReader.readTypeForUnitTest(status);
    assertTrue(t.toString().equals("xx"));
    assertTrue(status.nextToken().toString().equals("1:4: => (IDENTIFIER)"));
  }

  @Test
  public void testMissingArrow() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("a b", collector);
    Type t = CoraInputReader.readTypeForUnitTest(status);
    assertTrue(t.toString().equals("a"));
    assertTrue(status.nextToken().toString().equals("1:3: b (IDENTIFIER)"));
  }

  @Test
  public void testTypeMissingInputRecovery() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("-> b", collector);
    Type t = CoraInputReader.readTypeForUnitTest(status);
    assertTrue(t.toString().equals("b"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:1: Expected a type (started by a constant or bracket) but got ARROW (->).\n"));
  }

  @Test
  public void testTypeInputEmptyBracketsRecovery() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("() ⇒  b -> c", collector);
    Type t = CoraInputReader.readTypeForUnitTest(status);
    assertTrue(t.toString().equals("b ⇒ c"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:2: Expected a type (started by a constant or bracket) but got BRACKETCLOSE ()).\n"));
  }

  @Test
  public void testTypeMissingOutputRecovery() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("b -> c ⇒", collector);
    Type t = CoraInputReader.readTypeForUnitTest(status);
    assertTrue(t.toString().equals("b ⇒ c"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:9: Expected a type (started by a constant or bracket) but got end of input.\n"));
  }

  @Test
  public void testOutputEmptyBracketsRecovery() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("b -> ()", collector);
    Type t = CoraInputReader.readTypeForUnitTest(status);
    assertTrue(t.toString().equals("b"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:7: Expected a type (started by a constant or bracket) but got BRACKETCLOSE ()).\n"));
  }

  @Test
  public void testMissingClosingbracket() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("a -> (b ⇒ c \"", collector);
    Type t = CoraInputReader.readTypeForUnitTest(status);
    assertTrue(t.toString().equals("a ⇒ b ⇒ c"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:13: Incomplete string constant (ended by end of line).\n" +
      "1:13: Expected closing bracket but got STRING ().\n"));
  }

  @Test
  public void testMultipleTypeErrors() {
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus status = makeStatus("x -> ((a -> b c) ->) ->", collector);
    Type t = CoraInputReader.readTypeForUnitTest(status);
    assertTrue(t.toString().equals("x ⇒ a ⇒ b"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:15: Expected closing bracket but got IDENTIFIER (c).\n"));
    assertTrue(status.nextToken().toString().equals("1:15: c (IDENTIFIER)"));
  }
}

