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

import cora.exceptions.CustomParserError;
import cora.exceptions.IllegalArgumentError;
import cora.exceptions.NullInitialisationError;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class PositionTest {
  @Test
  public void testEmptyPosition() {
    Position pos = new EmptyPos();
    assertTrue(pos.toString().equals("ε"));
    assertTrue(pos.equals(new EmptyPos()));
    assertFalse(pos.equals(new ArgumentPos(1, new EmptyPos())));
    boolean ok = false;
    switch (pos) {
      case ArgumentPos(int i, Position tail): break;
      case MetaPos(int i, Position tail): break;
      case LambdaPos(Position tail): break;
      case EmptyPos(): ok = true;
    }
    assertTrue(ok);
  }

  @Test
  public void testArgumentPosition() {
    Position pos = new ArgumentPos(17, new MetaPos(2, new EmptyPos()));
    assertTrue(pos.toString().equals("17.!2.ε"));
    assertTrue(pos.equals(new ArgumentPos(17, new MetaPos(2, new EmptyPos()))));
    assertFalse(pos.equals(new ArgumentPos(17, new ArgumentPos(2, new EmptyPos()))));
    assertFalse(pos.equals(new MetaPos(17, new MetaPos(2, new EmptyPos()))));
    assertFalse(pos.equals(new ArgumentPos(18, new MetaPos(2, new EmptyPos()))));
    boolean ok = false;
    switch (pos) {
      case EmptyPos(): break;
      case MetaPos(int i, Position tail): break;
      case LambdaPos(Position tail): break;
      case ArgumentPos(int i, Position tail):
        ok = i == 17 && tail.toString().equals("!2.ε");
    }
    assertTrue(ok);
  }

  @Test
  public void testMetaPosition() {
    Position pos = new MetaPos(2, new LambdaPos(new EmptyPos()));
    assertTrue(pos.toString().equals("!2.0.ε"));
    assertTrue(pos.equals(new MetaPos(2, new LambdaPos(new EmptyPos()))));
    assertFalse(pos.equals(new MetaPos(2, new MetaPos(1, new EmptyPos()))));
    assertFalse(pos.equals(new ArgumentPos(2, new LambdaPos(new EmptyPos()))));
    assertFalse(pos.equals(new MetaPos(1, new LambdaPos(new EmptyPos()))));
    boolean ok = false;
    switch (pos) {
      case EmptyPos(): break;
      case ArgumentPos(int i, Position tail): break;
      case LambdaPos(Position tail): break;
      case MetaPos(int i, Position tail):
        ok = i == 2 && tail.toString().equals("0.ε");
    }
    assertTrue(ok);
  }

  @Test
  public void testLambdaPosition() {
    Position pos = new LambdaPos(new ArgumentPos(1, new EmptyPos()));
    assertTrue(pos.toString().equals("0.1.ε"));
    assertTrue(pos.equals(new LambdaPos(new ArgumentPos(1, new EmptyPos()))));
    assertFalse(pos.equals(new ArgumentPos(1, new EmptyPos())));
    boolean ok = false;
    switch (pos) {
      case EmptyPos(): break;
      case ArgumentPos(int i, Position tail): break;
      case MetaPos(int i, Position tail): break;
      case LambdaPos(Position tail): ok = tail.toString().equals("1.ε");
    }
    assertTrue(ok);
  }

  @Test
  public void testCreateWithIllegalindex() {
    assertThrows(IllegalArgumentError.class, () -> new ArgumentPos(0, new EmptyPos()));
    assertThrows(IllegalArgumentError.class, () -> new ArgumentPos(-1, new EmptyPos()));
    assertThrows(IllegalArgumentError.class, () -> new MetaPos(0, new EmptyPos()));
    assertThrows(IllegalArgumentError.class, () -> new MetaPos(-1, new EmptyPos()));
    new MetaPos(1000000, new EmptyPos()); // no error here
  }

  @Test
  public void testNullTail() {
    assertThrows(NullInitialisationError.class, () -> new ArgumentPos(12, null));
    assertThrows(NullInitialisationError.class, () -> new MetaPos(3, null));
    assertThrows(NullInitialisationError.class, () -> new LambdaPos(null));
  }

  @Test
  public void testCorrectParsing() {
    Position pos = Position.parse("5.6.7");
    assertTrue(pos.toString().equals("5.6.7.ε"));
    pos = Position.parse("19.!12.ε");
    assertTrue(pos.toString().equals("19.!12.ε"));
    pos = Position.parse("!2.1.");
    assertTrue(pos.toString().equals("!2.1.ε"));
    pos = Position.parse("0.19.12.ε");
    assertTrue(pos.toString().equals("0.19.12.ε"));
  }

  @Test
  public void testParseWithStar() {
    assertThrows(CustomParserError.class, () -> Position.parse("1.254.*3.☆15"));
    assertThrows(CustomParserError.class, () -> Position.parse("3.111.☆2"));
  }

  @Test
  public void testIllegalParsing() {
    assertThrows(CustomParserError.class, () -> Position.parse("1..254"));
    assertThrows(CustomParserError.class, () -> Position.parse("1.254.3.."));
    assertThrows(CustomParserError.class, () -> Position.parse("19.-1.12.ε"));
    assertThrows(CustomParserError.class, () -> Position.parse("5.1@.3"));
  }
}

