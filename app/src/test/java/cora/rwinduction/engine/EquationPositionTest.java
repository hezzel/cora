/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rwinduction.engine;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.Set;

import charlie.exceptions.CustomParserException;
import charlie.terms.position.Position;

class EquationPositionTest {
  @Test
  public void testParseWithoutPosition() throws CustomParserException {
    EquationPosition pos = EquationPosition.parse("");
    assertTrue(pos.equals(EquationPosition.TOPLEFT));
    assertFalse(pos.equals(EquationPosition.TOPRIGHT));

    pos = EquationPosition.parse("L");
    assertTrue(pos.equals(EquationPosition.TOPLEFT));
    assertFalse(pos.equals(EquationPosition.TOPRIGHT));

    pos = EquationPosition.parse("R");
    assertTrue(pos.equals(EquationPosition.TOPRIGHT));
    assertFalse(pos.equals(EquationPosition.TOPLEFT));

    pos = EquationPosition.parse("Lε");
    assertTrue(pos.equals(EquationPosition.TOPLEFT));

    pos = EquationPosition.parse("R.");
    assertTrue(pos.equals(EquationPosition.TOPRIGHT));
  }

  @Test
  public void testParseWithPosition() throws CustomParserException {
    EquationPosition pos = EquationPosition.parse("L.1.2.ε");
    assertTrue(pos.querySide() == EquationPosition.Side.Left);
    assertTrue(pos.queryPosition().toString().equals("1.2"));

    pos = EquationPosition.parse("R.3");
    assertTrue(pos.querySide() == EquationPosition.Side.Right);
    assertTrue(pos.queryPosition().toString().equals("3"));

    pos = EquationPosition.parse("1.2");
    assertTrue(pos.querySide() == EquationPosition.Side.Left);
    assertTrue(pos.queryPosition().toString().equals("1.2"));
  }

  @Test
  public void testParsePartial() throws CustomParserException {
    EquationPosition pos = EquationPosition.parse("1.2.*3");
    assertTrue(pos.querySide() == EquationPosition.Side.Left);
    assertTrue(pos.queryPosition().toString().equals("1.2.☆3"));

    pos = EquationPosition.parse("R*5");
    assertTrue(pos.querySide() == EquationPosition.Side.Right);
    assertTrue(pos.queryPosition().toString().equals("☆5"));
  }
}

