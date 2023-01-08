/**************************************************************************************************
 Copyright 2022, 2023 Cynthia Kop 

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the 
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.terms;

import org.junit.Test;
import static org.junit.Assert.*;

public class PositionTest {
  @Test
  public void testEmptyPosition() {
    Position pos = new EmptyPosition();
    assertTrue(pos.toString().equals("ε"));
    assertTrue(pos.equals(new EmptyPosition()));
    assertTrue(pos.equals(new EmptyPath(TermFactory.createVar("y"))));
    assertFalse(pos.equals(new ConsPosition(1, new EmptyPosition())));
    assertTrue(pos.isEmpty());
    assertFalse(pos.isArgument());
  }

  @Test
  public void testEmptyPath() {
    Term s = TermFactory.createConstant("c", 1).apply(TermFactory.createVar("x"));
    Path p = new EmptyPath(s);
    Position pos = p;
    assertTrue(pos.toString().equals("ε"));
    assertTrue(pos.equals(new EmptyPosition()));
    assertTrue(pos.equals(new EmptyPath(TermFactory.createConstant("a", 0))));
    assertFalse(pos.equals(new ArgumentPath(s, 1, new EmptyPath(s.queryArgument(1)))));
    assertTrue(pos.isEmpty());
    assertFalse(pos.isArgument());
    assertTrue(p.queryAssociatedTerm() == s);
    assertTrue(p.queryCorrespondingSubterm() == s);
  }

  @Test(expected = cora.exceptions.InappropriatePatternDataError.class)
  public void testNoArgument() {
    Position pos = new EmptyPosition();
    pos.queryArgumentPosition();
  }

  @Test(expected = cora.exceptions.InappropriatePatternDataError.class)
  public void testPositionNoTail() {
    Position pos = new EmptyPosition();
    pos.queryTail();
  }

  @Test(expected = cora.exceptions.InappropriatePatternDataError.class)
  public void testPathNoTail() {
    Position pos = new EmptyPosition();
    pos.queryTail();
  }

  @Test
  public void testConsPosition() {
    Position pos = new ConsPosition(1, new ConsPosition(2, new EmptyPosition()));
    assertTrue(pos.toString().equals("1.2.ε"));
    assertTrue(pos.queryArgumentPosition() == 1);
    assertTrue(pos.queryTail().queryArgumentPosition() == 2);
    assertFalse(pos.isEmpty());
    assertTrue(pos.isArgument());
    Term fgab = TermFactory.createConstant("f", 1).apply(
      TermFactory.createConstant("g", 2).apply(TermFactory.createConstant("a", 0)).apply(
      TermFactory.createConstant("b", 0)));
    Path path = new ArgumentPath(fgab, 1,
      new ArgumentPath(fgab.queryArgument(1), 2,
      new EmptyPath(TermFactory.createConstant("b", 0))));
    assertTrue(pos.equals(path));
  }

  @Test
  public void testArgumentPath() {
    Term fgab = TermFactory.createConstant("f", 1).apply(
      TermFactory.createConstant("g", 2).apply(TermFactory.createConstant("a", 0)).apply(
      TermFactory.createConstant("b", 0)));
    Path path = new ArgumentPath(fgab, 1,
      new ArgumentPath(fgab.queryArgument(1), 2,
      new EmptyPath(TermFactory.createConstant("b", 0))));
    assertTrue(path.toString().equals("1.2.ε"));
    assertTrue(path.queryArgumentPosition() == 1);
    assertTrue(path.queryTail().queryArgumentPosition() == 2);
    assertFalse(path.isEmpty());
    assertTrue(path.isArgument());
    Position pos = new ConsPosition(1, new ConsPosition(2, new EmptyPosition()));
    assertTrue(path.equals(pos));
    assertTrue(path.queryAssociatedTerm() == fgab);
    assertTrue(path.queryCorrespondingSubterm().equals(TermFactory.createConstant("b", 0)));
  }

  @Test
  public void testCorrectParsing() {
    Position pos = PositionFactory.parsePos("5.6.7");
    assertTrue(pos.toString().equals("5.6.7.ε"));
    pos = PositionFactory.parsePos("19.12.ε");
    assertTrue(pos.toString().equals("19.12.ε"));
    pos = PositionFactory.parsePos("2.1.");
    assertTrue(pos.toString().equals("2.1.ε"));
  }

  @Test(expected = cora.exceptions.ParserError.class)
  public void testParseWithAsciiStar() {
    PositionFactory.parsePos("1.254.*3.☆15");
  }

  @Test(expected = cora.exceptions.ParserError.class)
  public void testParseWithUniStar() {
    PositionFactory.parsePos(("3.111.☆2"));
  }

  @Test(expected = cora.exceptions.ParserError.class)
  public void testParseWithEmptyIndex() {
    PositionFactory.parsePos("1..254");
  }

  @Test(expected = cora.exceptions.ParserError.class)
  public void testParseWithEmptyIndexAtTheEnd() {
    PositionFactory.parsePos("1.254.3..");
  }

  @Test(expected = cora.exceptions.ParserError.class)
  public void testParseWithZeroIndex() {
    PositionFactory.parsePos("0.19.12.ε");
  }

  @Test(expected = cora.exceptions.ParserError.class)
  public void testParseWithNegativeIndex() {
    PositionFactory.parsePos("19.-1.12.ε");
  }

  @Test(expected = cora.exceptions.ParserError.class)
  public void testParseWithIllegalCharacter() {
    PositionFactory.parsePos("5.1@.3");
  }
}

