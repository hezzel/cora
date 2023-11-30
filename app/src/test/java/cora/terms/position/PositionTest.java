/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.terms.position;

import cora.exceptions.*;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class PositionTest {
  @Test
  public void testEmptyPosition() {
    Position pos = Position.empty;
    assertTrue(pos.toString().equals("ε"));
    assertTrue(pos.equals(new FinalPos(0)));
    assertFalse(pos.equals(new FinalPos(1)));
    assertFalse(pos.equals(new ArgumentPos(1, new FinalPos(0))));
    assertTrue(pos.isEmpty());
    assertTrue(pos.isFinal());
    assertTrue(pos.queryChopCount() == 0);
    assertThrows(InappropriatePatternDataError.class, () -> pos.queryHead());
    assertThrows(InappropriatePatternDataError.class, () -> pos.queryTail());
    
    boolean ok = false;
    switch (pos) {
      case ArgumentPos(int i, Position tail): break;
      case MetaPos(int i, Position tail): break;
      case LambdaPos(Position tail): break;
      case FinalPos(int k): ok = k == 0;
    }
    assertTrue(ok);
  }

  @Test
  public void testFinalPosition() {
    Position pos = new FinalPos(3);
    assertTrue(pos.toString().equals("☆3"));
    assertTrue(pos.equals(new FinalPos(3)));
    assertFalse(pos.equals(new FinalPos(2)));
    assertFalse(pos.equals(new LambdaPos(new FinalPos(3))));
    assertFalse(pos.isEmpty());
    assertTrue(pos.isFinal());
    assertTrue(pos.queryChopCount() == 3);
    assertThrows(InappropriatePatternDataError.class, () -> pos.queryHead());
    assertThrows(InappropriatePatternDataError.class, () -> pos.queryTail());
    
    boolean ok = false;
    switch (pos) {
      case ArgumentPos(int i, Position tail): break;
      case MetaPos(int i, Position tail): break;
      case LambdaPos(Position tail): break;
      case FinalPos(int k): ok = k == 3;
    }
    assertTrue(ok);
  }

  @Test
  public void testArgumentPosition() {
    Position pos = new ArgumentPos(17, new MetaPos(2, new FinalPos(0)));
    assertTrue(pos.toString().equals("17.!2.ε"));
    assertTrue(pos.equals(new ArgumentPos(17, new MetaPos(2, Position.empty))));
    assertFalse(pos.equals(new ArgumentPos(17, new ArgumentPos(2, new FinalPos(0)))));
    assertFalse(pos.equals(new MetaPos(17, new MetaPos(2, Position.empty))));
    assertFalse(pos.equals(new ArgumentPos(18, new MetaPos(2, Position.empty))));
    assertFalse(pos.isEmpty());
    assertFalse(pos.isFinal());
    assertTrue(pos.queryHead() == 17);
    assertTrue(pos.queryTail().equals(new MetaPos(2, new FinalPos(0))));
    
    boolean ok = false;
    switch (pos) {
      case FinalPos(int k): break;
      case MetaPos(int i, Position tail): break;
      case LambdaPos(Position tail): break;
      case ArgumentPos(int i, Position tail):
        ok = i == 17 && tail.toString().equals("!2.ε");
    }
    assertTrue(ok);
  }

  @Test
  public void testMetaPosition() {
    Position pos = new MetaPos(2, new LambdaPos(new FinalPos(9)));
    assertTrue(pos.toString().equals("!2.0.☆9"));
    assertTrue(pos.equals(new MetaPos(2, new LambdaPos(new FinalPos(9)))));
    assertFalse(pos.equals(new MetaPos(2, new MetaPos(1, new FinalPos(9)))));
    assertFalse(pos.equals(new MetaPos(2, new LambdaPos(new FinalPos(8)))));
    assertFalse(pos.equals(new ArgumentPos(2, new LambdaPos(new FinalPos(9)))));
    assertFalse(pos.equals(new MetaPos(1, new LambdaPos(new FinalPos(9)))));
    assertFalse(pos.isEmpty());
    assertFalse(pos.isFinal());
    assertTrue(pos.queryHead() == -2);
    assertTrue(pos.queryTail().equals(new LambdaPos(new FinalPos(9))));

    boolean ok = false;
    switch (pos) {
      case FinalPos(int k): break;
      case ArgumentPos(int i, Position tail): break;
      case LambdaPos(Position tail): break;
      case MetaPos(int i, Position tail):
        ok = i == 2 && tail.toString().equals("0.☆9");
    }
    assertTrue(ok);
  }

  @Test
  public void testLambdaPosition() {
    Position pos = new LambdaPos(new ArgumentPos(1, Position.empty));
    assertTrue(pos.toString().equals("0.1.ε"));
    assertTrue(pos.equals(new LambdaPos(new ArgumentPos(1, Position.empty))));
    assertFalse(pos.equals(new ArgumentPos(1, Position.empty)));
    assertTrue(pos.queryHead() == 0);
    assertTrue(pos.queryTail().equals(new ArgumentPos(1, Position.empty)));

    boolean ok = false;
    switch (pos) {
      case FinalPos(int k): break;
      case ArgumentPos(int i, Position tail): break;
      case MetaPos(int i, Position tail): break;
      case LambdaPos(Position tail): ok = tail.toString().equals("1.ε");
    }
    assertTrue(ok);
  }

  @Test
  public void testCreateWithIllegalindex() {
    assertThrows(IllegalArgumentError.class, () -> new FinalPos(-1));
    assertThrows(IllegalArgumentError.class, () -> new ArgumentPos(0, Position.empty));
    assertThrows(IllegalArgumentError.class, () -> new ArgumentPos(-1, Position.empty));
    assertThrows(IllegalArgumentError.class, () -> new MetaPos(0, Position.empty));
    assertThrows(IllegalArgumentError.class, () -> new MetaPos(-1, Position.empty));
    new MetaPos(1000000, Position.empty); // no error here
  }

  @Test
  public void testNullTail() {
    assertThrows(NullInitialisationError.class, () -> new ArgumentPos(12, null));
    assertThrows(NullInitialisationError.class, () -> new MetaPos(3, null));
    assertThrows(NullInitialisationError.class, () -> new LambdaPos(null));
  }

  @Test
  public void testCorrectFullPositionParsing() {
    Position pos = Position.parse("5.6.7");
    assertTrue(pos.toString().equals("5.6.7.ε"));
    pos = Position.parse("19.!12.ε");
    assertTrue(pos.toString().equals("19.!12.ε"));
    pos = Position.parse("!2.1.");
    assertTrue(pos.toString().equals("!2.1.ε"));
    pos = Position.parse("0.19.12.ε");
    assertTrue(pos.toString().equals("0.19.12.ε"));
    pos = Position.parse("19.-1.12.ε");
    assertTrue(pos.toString().equals("19.!1.12.ε"));
  }

  @Test
  public void testCorrectPartialPositionParsing() {
    Position pos = Position.parse("1.254.3.*15");
    assertTrue(pos.toString().equals("1.254.3.☆15"));
    pos = Position.parse(("3.111.☆2"));
    assertTrue(pos.toString().equals("3.111.☆2"));
  }

  @Test
  public void testIncorrectParsing() {
    assertThrows(CustomParserError.class, () -> Position.parse("1.254.*3.☆15"));
    assertThrows(CustomParserError.class, () -> Position.parse("3.111.☆2ε"));
    assertThrows(CustomParserError.class, () -> Position.parse("3.111.☆2.ε"));
    assertThrows(CustomParserError.class, () -> Position.parse("1..254"));
    assertThrows(CustomParserError.class, () -> Position.parse("5.1@.3"));
    assertThrows(CustomParserError.class, () -> Position.parse("1.254.3.."));
  }
}

