/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

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

import charlie.exceptions.ParseException;
import charlie.types.*;
import charlie.parser.lib.ErrorCollector;
import charlie.parser.Parser.*;

public class CoraTypesParsingTest {
  @Test
  public void testReadConstantBaseType() {
    Type t = CoraParser.readType("aKKaO");
    assertTrue(t.isBaseType());
    assertFalse(t.isTheoryType());
    assertTrue(t.toString().equals("aKKaO"));
  }

  @Test
  public void testReadInt() {
    Type t = CoraParser.readType("Int");
    assertTrue(t.toString().equals("Int"));
    assertTrue(t.isTheoryType());
    assertTrue(CoraParser.readType("Int", true, null).isTheoryType());
    assertFalse(CoraParser.readType("Int", false, null).isTheoryType());
  }

  @Test
  public void testReadBool() {
    Type t = CoraParser.readType("Bool", true, null);
    assertTrue(t.toString().equals("Bool"));
    assertTrue(t.isTheoryType());
    t = CoraParser.readType("Bool", false, null);
    assertTrue(t.toString().equals("Bool"));
    assertFalse(t.isTheoryType());
  }

  @Test
  public void testReadString() {
    Type t = CoraParser.readType("String");
    assertTrue(t.toString().equals("String"));
    assertTrue(t.isTheoryType());
  }

  @Test
  public void testSimpleArrowType() {
    Type t = CoraParser.readType("xx → yy");
    assertTrue(t.isArrowType());
    assertTrue(t.subtype(1).toString().equals("xx"));
    assertTrue(t.subtype(2).toString().equals("yy"));
  }

  @Test
  public void testSimpleArrowTypeWithPlainArrow() {
    Type t = CoraParser.readType("xx -> yy");
    assertTrue(t.isArrowType());
    assertTrue(t.subtype(1).toString().equals("xx"));
    assertTrue(t.subtype(2).toString().equals("yy"));
  }

  @Test
  public void testSimpleProductType() {
    Type t1 = CoraParser.readType("⦇ xx, yy, zz ⦈", true, null);
    Type t2 = CoraParser.readType("⦇ xx , yy ,zz ⦈", false, null);
    assertTrue(t1.equals(t2));
    assertTrue(t1.isProductType());
    assertTrue(t1.numberSubtypes() == 3);
    assertTrue(t1.subtype(1).toString().equals("xx"));
    assertTrue(t1.subtype(2).toString().equals("yy"));
    assertTrue(t1.subtype(3).toString().equals("zz"));
  }

  @Test
  public void testRightAssociativeType() {
    Type t = CoraParser.readType("xx -> yy → zz");
    assertTrue(t.isArrowType());
    assertTrue(t.subtype(1).toString().equals("xx"));
    assertTrue(t.subtype(2).isArrowType());
    assertTrue(t.subtype(2).toString().equals("yy → zz"));
  }

  @Test
  public void testMixedType() {
    Type t = CoraParser.readType("⦇ a , b ⦈ -> (|c,d|)");
    assertTrue(t.isArrowType());
    assertTrue(t.subtype(1).isProductType());
    assertTrue(t.subtype(1).toString().equals("⦇ a, b ⦈"));
    assertTrue(t.subtype(2).isProductType());
    assertTrue(t.subtype(2).toString().equals("⦇ c, d ⦈"));
  }

  @Test
  public void testHigherArrowType() {
    Type t = CoraParser.readType("(xx -> ⦇ yy, xx|)) -> zz");
    assertTrue(t.isArrowType());
    assertTrue(t.subtype(1).isArrowType());
    assertTrue(t.subtype(1).toString().equals("xx → ⦇ yy, xx ⦈"));
    assertTrue(t.subtype(2).toString().equals("zz"));
  }

  @Test
  public void testHigherProductType() {
    Type t = CoraParser.readType("(|xx -> (|yy ,xx|), zz|)");
    assertTrue(t.isProductType());
    assertTrue(t.subtype(1).isArrowType());
    assertTrue(t.subtype(1).toString().equals("xx → ⦇ yy, xx ⦈"));
    assertTrue(t.subtype(2).toString().equals("zz"));
  }

  @Test
  public void testUnnecessaryHigherType() {
    Type t = CoraParser.readType("(a) -> b");
    assertTrue(t.isArrowType());
    assertTrue(t.subtype(1).toString().equals("a"));
    assertTrue(t.subtype(2).toString().equals("b"));
  }

  @Test
  public void testReadTypeWithBracketsInTheMiddle() {
    Type t = CoraParser.readType("a -> (b -> cd) -> e");
    assertTrue(t.isArrowType());
    assertTrue(t.toString().equals("a → (b → cd) → e"));
  }

  @Test
  public void testReadTypeEndingWithBrackets() {
    Type t = CoraParser.readType("(|a,b|) → (c -> d → e)");
    assertTrue(t.isArrowType());
    assertTrue(t.subtype(1).toString().equals("⦇ a, b ⦈"));
    assertTrue(t.subtype(2).toString().equals("c → d → e"));
  }

  @Test
  public void testReadTheoryArrowType() {
    Type t = CoraParser.readType("Int -> (Bool -> Int) → String");
    assertTrue(t.toString().equals("Int → (Bool → Int) → String"));
    assertTrue(t.isTheoryType());
  }

  @Test
  public void testReadTypeWithDoubleArrowRecovery() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("a -> b -> -> c", false, collector);
    assertTrue(t.toString().equals("a → b → c"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:11: Expected a type (started by a sort identifier or bracket) but got ARROW (->).\n"));
  }

  @Test
  public void testArrowTypeWithNonExistingArrowIsRequested() {
    assertThrows(ParseException.class, () -> CoraParser.readType("xx => yy"));
  }

  @Test
  public void testMissingArrow() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("a b", true, collector);
    assertTrue(t.toString().equals("a"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:3: Expected end of input but got IDENTIFIER (b).\n"));
  }

  @Test
  public void testTypeMissingInputRecovery() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("-> Int", true, collector);
    assertTrue(t.toString().equals("Int"));
    assertTrue(t.isTheoryType());
    assertTrue(collector.queryCollectedMessages().equals(
      "1:1: Expected a type (started by a sort identifier or bracket) but got ARROW (->).\n"));
  }

  @Test
  public void testTypeInputEmptyBracketsRecovery() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("() →  b -> c", false, collector);
    assertTrue(t.toString().equals("b → c"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:2: Expected a type (started by a sort identifier or bracket) but got BRACKETCLOSE ()).\n"));
  }

  @Test
  public void testTypeMissingOutputRecovery() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("b -> c →", true, collector);
    assertTrue(t.toString().equals("b → c"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:9: Expected a type (started by a sort identifier or bracket) but got end of input.\n"));
  }

  @Test
  public void testTypeMissingTupleCloseBracketRecovery() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("(| b , c ) -> d", true, collector);
    assertTrue(t.toString().equals("⦇ b, c ⦈ → d"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:10: Expected tuple closing bracket but got BRACKETCLOSE ()).\n"));
  }

  @Test
  public void testOutputEmptyBracketsRecovery() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("String -> ()", false, collector);
    assertTrue(t.toString().equals("String"));
    assertTrue(t.isBaseType());
    assertFalse(t.isTheoryType());
    assertTrue(collector.queryCollectedMessages().equals(
      "1:12: Expected a type (started by a sort identifier or bracket) but got BRACKETCLOSE ()).\n"));
  }

  @Test
  public void testMissingClosingbracket() {
    ErrorCollector collector = new ErrorCollector();
    Type t = CoraParser.readType("a -> (b → c \"", true, collector);
    assertTrue(t.toString().equals("a → b → c"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:13: Incomplete string constant (ended by end of line).\n" +
      "1:13: Expected closing bracket but got STRING (\"\").\n"));
  }

  @Test
  public void testMultipleTypeErrors() {
    ErrorCollector collector = new ErrorCollector(10);
    Type t = CoraParser.readType("x -> ((a -> b c) ×) ->", false, collector);
    assertTrue(t.toString().equals("x → a → b"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:15: Expected closing bracket but got IDENTIFIER (c).\n"));
  }
}

