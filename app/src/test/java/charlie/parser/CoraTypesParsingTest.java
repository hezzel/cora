/**************************************************************************************************
 Copyright 2023--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.parser;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.types.*;
import charlie.parser.lib.ParsingException;
import charlie.parser.lib.ErrorCollector;
import charlie.parser.Parser.*;
import charlie.theory.Theory;

public class CoraTypesParsingTest {
  @Test
  public void testReadConstantBaseType() {
    Type t = CoraParser.readType("aKKaO");
    assertTrue(t.isBaseType());
    assertFalse(Theory.isTheory(t));
    assertTrue(t.toString().equals("aKKaO"));
  }

  @Test
  public void testReadInt() {
    Type t = CoraParser.readType("Int");
    assertTrue(t.toString().equals("Int"));
    assertTrue(Theory.isTheory(t));
    assertTrue(Theory.isTheory(CoraParser.readType("Int", true, null)));
    assertFalse(Theory.isTheory(CoraParser.readType("Int", false, null)));
  }

  @Test
  public void testReadBool() {
    Type t = CoraParser.readType("Bool", true, null);
    assertTrue(t.toString().equals("Bool"));
    assertTrue(Theory.isTheory(t));
    t = CoraParser.readType("Bool", false, null);
    assertTrue(t.toString().equals("Bool"));
    assertFalse(Theory.isTheory(t));
  }

  @Test
  public void testReadString() {
    Type t = CoraParser.readType("String");
    assertTrue(t.toString().equals("String"));
    assertTrue(Theory.isTheory(t));
  }

  @Test
  public void testSimpleArrowType() {
    Type t = CoraParser.readType("xx → yy");
    assertTrue(t.isArrowType());
    assertTrue(t.querySubtype(1).toString().equals("xx"));
    assertTrue(t.querySubtype(2).toString().equals("yy"));
  }

  @Test
  public void testSimpleArrowTypeWithPlainArrow() {
    Type t = CoraParser.readType("xx -> yy");
    assertTrue(t.isArrowType());
    assertTrue(t.querySubtype(1).toString().equals("xx"));
    assertTrue(t.querySubtype(2).toString().equals("yy"));
  }

  @Test
  public void testTypeVariable() {
    Type t = CoraParser.readType("$alpha");
    assertTrue(t.isVariableType());
  }

  @Test
  public void testTypeVariableWithBrackets() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("$a() -> b", true, collector);
    assertTrue(t.toString().equals("$a → b"));
    assertTrue(collector.toString().equals(
      "1:3: Unexpected bracket following type variable.\n"));
  }

  @Test
  public void testSimpleDataType() {
    Type t1 = CoraParser.readType("d(xx, yy, zz)", true, null);
    Type t2 = CoraParser.readType("d(xx , yy ,zz )", false, null);
    assertTrue(t1.equals(t2));
    assertTrue(t1.isDataType());
    assertTrue(t1.queryNumberSubtypes() == 3);
    assertTrue(t1.querySubtype(1).toString().equals("xx"));
    assertTrue(t1.querySubtype(2).toString().equals("yy"));
    assertTrue(t1.querySubtype(3).toString().equals("zz"));
  }

  @Test
  public void testRightAssociativeType() {
    Type t = CoraParser.readType("xx -> yy → zz");
    assertTrue(t.isArrowType());
    assertTrue(t.querySubtype(1).toString().equals("xx"));
    assertTrue(t.querySubtype(2).isArrowType());
    assertTrue(t.querySubtype(2).toString().equals("yy → zz"));
  }

  @Test
  public void testMixedType() {
    Type t = CoraParser.readType("pair(a , b) -> pair($a,d)");
    assertTrue(t.isArrowType());
    assertTrue(t.querySubtype(1).isDataType());
    assertTrue(t.querySubtype(1).toString().equals("pair(a, b)"));
    assertTrue(t.querySubtype(2).isDataType());
    assertTrue(t.querySubtype(2).toString().equals("pair($a, d)"));
  }

  @Test
  public void testHigherArrowType() {
    Type t = CoraParser.readType("(xx() -> pair(yy, xx)) -> zz");
    assertTrue(t.isArrowType());
    assertTrue(t.querySubtype(1).isArrowType());
    assertTrue(t.querySubtype(1).toString().equals("xx → pair(yy, xx)"));
    assertTrue(t.querySubtype(2).toString().equals("zz"));
  }

  @Test
  public void testHigherDataType() {
    Type t = CoraParser.readType("c(xx -> d(yy ,xx), zz)");
    assertTrue(t.isDataType());
    assertTrue(t.querySubtype(1).isArrowType());
    assertTrue(t.querySubtype(1).toString().equals("xx → d(yy, xx)"));
    assertTrue(t.querySubtype(2).toString().equals("zz"));
  }

  @Test
  public void testUnnecessaryHigherType() {
    Type t = CoraParser.readType("(a) -> b");
    assertTrue(t.isArrowType());
    assertTrue(t.querySubtype(1).toString().equals("a"));
    assertTrue(t.querySubtype(2).toString().equals("b"));
  }

  @Test
  public void testReadTypeWithBracketsInTheMiddle() {
    Type t = CoraParser.readType("a -> (b -> cd) -> e");
    assertTrue(t.isArrowType());
    assertTrue(t.toString().equals("a → (b → cd) → e"));
  }

  @Test
  public void testReadTypeEndingWithBrackets() {
    Type t = CoraParser.readType("pair(a,b) → (c -> $d → e)");
    assertTrue(t.isArrowType());
    assertTrue(t.querySubtype(1).toString().equals("pair(a, b)"));
    assertTrue(t.querySubtype(2).toString().equals("c → $d → e"));
    assertTrue(t.querySubtype(2).querySubtype(2).querySubtype(1).isVariableType());
  }

  @Test
  public void testReadTheoryArrowType() {
    Type t = CoraParser.readType("Int -> (Bool -> Int) → String");
    assertTrue(t.toString().equals("Int → (Bool → Int) → String"));
    assertTrue(Theory.isTheory(t));
  }

  @Test
  public void testReadTypeWithDoubleArrowRecovery() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("a -> b -> -> c", false, collector);
    assertTrue(t.toString().equals("a → b → c"));
    assertTrue(collector.toString().equals(
      "1:11: Expected a type (started by a sort constructor or bracket) but got ARROW (->).\n"));
  }

  @Test
  public void testArrowTypeWithNonExistingArrowIsRequested() {
    assertThrows(ParsingException.class, () -> CoraParser.readType("xx => yy"));
  }

  @Test
  public void testMissingArrow() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("a b", true, collector);
    assertTrue(t.toString().equals("a"));
    assertTrue(collector.toString().equals(
      "1:3: Expected end of input but got IDENTIFIER (b).\n"));
  }

  @Test
  public void testTypeMissingInputRecovery() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("-> Int", true, collector);
    assertTrue(t.toString().equals("Int"));
    assertTrue(Theory.isTheory(t));
    assertTrue(collector.toString().equals(
      "1:1: Expected a type (started by a sort constructor or bracket) but got ARROW (->).\n"));
  }

  @Test
  public void testTypeInputEmptyBracketsRecovery() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("() →  b -> c", false, collector);
    assertTrue(t.toString().equals("b → c"));
    assertTrue(collector.toString().equals("1:2: Expected a type (started by a sort constructor " +
      "or bracket) but got BRACKETCLOSE ()).\n"));
  }

  @Test
  public void testTypeMissingOutputRecovery() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("b -> c →", true, collector);
    assertTrue(t.toString().equals("b → c"));
    assertTrue(collector.toString().equals(
      "1:9: Expected a type (started by a sort constructor or bracket) but got end of input.\n"));
  }

  @Test
  public void testTypeMissingDataCloseBracketRecovery() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("pair(b , c d", true, collector);
    assertTrue(t.toString().equals("pair(b, c)"));
    assertTrue(collector.toString().equals(
      "1:12: Expected closing bracket but got IDENTIFIER (d).\n"));
  }

  @Test
  public void testOutputEmptyBracketsRecovery() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("String -> ()", false, collector);
    assertTrue(t.toString().equals("String"));
    assertTrue(t.isBaseType());
    assertFalse(Theory.isTheory(t));
    assertTrue(collector.toString().equals("1:12: Expected a type (started by a sort " +
      "constructor or bracket) but got BRACKETCLOSE ()).\n"));
  }

  @Test
  public void testMissingClosingbracket() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("a -> (b → c \"", true, collector);
    assertTrue(t.toString().equals("a → b → c"));
    assertTrue(collector.toString().equals(
      "1:13: Incomplete string constant (ended by end of line).\n" +
      "1:13: Expected closing bracket but got STRING (\"\").\n"));
  }

  @Test
  public void testMultipleTypeErrors() {
    ErrorCollector collector = new ErrorCollector(10);
    Type t = CoraParser.readType("x -> ((a -> b c) ×) ->", false, collector);
    assertTrue(t.toString().equals("x → a → b"));
    assertTrue(collector.toString().equals(
      "1:15: Expected closing bracket but got IDENTIFIER (c).\n"));
  }
}

