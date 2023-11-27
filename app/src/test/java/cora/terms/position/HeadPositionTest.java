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

public class HeadPositionTest {
  @Test
  public void testIllegalCreation() {
    assertThrows(NullInitialisationError.class, () -> new HeadPosition(null, 1));
    assertThrows(IllegalArgumentError.class, () -> new HeadPosition(new EmptyPos(), -1));
  }

  @Test
  public void testEmptyHeadPosition() {
    HeadPosition hpos = new HeadPosition(new EmptyPos());
    assertTrue(hpos.queryChopCount() == 0);
    assertTrue(hpos.queryPosition().toString().equals("ε"));
    assertTrue(hpos.toString().equals("ε"));
    assertTrue(hpos.equals(new HeadPosition(new EmptyPos(), 0)));
  }

  @Test
  public void testImmediateHeadPosition() {
    HeadPosition hpos = new HeadPosition(new EmptyPos(), 3);
    assertTrue(hpos.queryPosition().toString().equals("ε"));
    assertTrue(hpos.queryChopCount() == 3);
    assertFalse(hpos.equals(new HeadPosition(new EmptyPos())));
    assertTrue(hpos.equals(new HeadPosition(new EmptyPos(), 3)));
    assertTrue(hpos.toString().equals("☆3"));
  }

  @Test
  public void testArgumentHeadPosition() {
    Position pos = new ArgumentPos(1, new ArgumentPos(2, new EmptyPos()));
    HeadPosition hpos = new HeadPosition(pos, 2);
    HeadPosition hpos2 = new HeadPosition(pos);
    assertTrue(hpos.toString().equals("1.2.☆2"));
    assertTrue(hpos2.toString().equals("1.2.ε"));
    switch (hpos) {
      case HeadPosition(Position p, int c):
        assertTrue(c == 2);
        assertTrue(p.toString().equals("1.2.ε"));
    }
  }

  @Test
  public void testCorrectParsing() {
    HeadPosition hpos = HeadPosition.parse("1.254.3.*15");
    assertTrue(hpos.toString().equals("1.254.3.☆15"));
    hpos = HeadPosition.parse("5.6.7");
    assertTrue(hpos.toString().equals("5.6.7.ε"));
    hpos = HeadPosition.parse("19.0.12.ε");
    assertTrue(hpos.toString().equals("19.0.12.ε"));
    hpos = HeadPosition.parse(("3.111.☆2"));
    assertTrue(hpos.toString().equals("3.111.☆2"));
    hpos = HeadPosition.parse("2.1.");
    assertTrue(hpos.toString().equals("2.1.ε"));
  }

  @Test
  public void testIncorrectParsing() {
    assertThrows(CustomParserError.class, () -> HeadPosition.parse("1.254.*3.☆15"));
    assertThrows(CustomParserError.class, () -> HeadPosition.parse("1..254.*3"));
    assertThrows(CustomParserError.class, () -> HeadPosition.parse("1.254.3.."));
    assertThrows(CustomParserError.class, () -> HeadPosition.parse("5.1@.3.ε"));
  }
}

