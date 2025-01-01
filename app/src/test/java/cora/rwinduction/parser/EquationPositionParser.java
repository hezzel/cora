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

package cora.rwinduction.parser;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.exceptions.CustomParserException;
import charlie.exceptions.ParseException;
import charlie.parser.lib.ParsingStatus;
import cora.rwinduction.engine.EquationPosition;

class EquationPositionParserTest {
  private void testEquals(String input, String output) {
    ParsingStatus status = RWParser.createStatus(input);
    EquationPosition position = null;
    try { position = EquationPositionParser.readPosition(status); }
    catch (CustomParserException e) { assertTrue(false, "exception parsing " + input); }
    assertTrue(position != null, "incorrect token on input " + input);
    assertTrue(position.toString().equals(output),
      "parsing " + input + " yields " + position.toString() + " instead of " + output);
    assertTrue(status.peekNext().isEof(), "position " + input + " not fully read");
  }

  @Test
  public void testEmptyPosition() {
    testEquals("ε", "L");
    testEquals("e", "L");
    testEquals(".e", "L");
  }

  @Test
  public void testLeftRight() {
    testEquals("L", "L");
    testEquals("R", "R");
    testEquals("Lε", "L");
    testEquals("R.ε", "R");
  }

  @Test
  public void testLongerPositions() {
    testEquals("L1.3.ε", "L1.3");
    testEquals("R.9.4", "R9.4");
    testEquals("R.9.12.-2.0.4", "R9.12.!2.0.4");
    testEquals("17.9.!4.e", "L17.9.!4");
  }

  @Test
  public void testPartialPositions() {
    testEquals("L2.☆4", "L2.☆4");
    testEquals("R.*9", "R.☆9");
    testEquals("0.*9", "L0.☆9");
    testEquals("R7.0.*9", "R7.0.☆9");
  }

  @Test
  public void testNotAnEquationPosition() {
    assertTrue(RWParser.createStatus("0*9").nextToken().toString().equals("1:1: 0 (INTEGER)"));
    assertTrue(RWParser.createStatus("L.L").nextToken().toString().equals("1:1: L (IDENTIFIER)"));
  }
}

