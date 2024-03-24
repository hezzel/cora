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

package charlie.parser.lib;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class TokenTest {
  @Test
  public void testToken() {
    ParsePosition position = new ParsePosition("test.trs", 3, 9);
    Token token = new Token(position, "IDENTIFIER", "counter");
    assertFalse(token.isEof());
    assertTrue(token.getName().equals("IDENTIFIER"));
    assertTrue(token.getText().equals("counter"));
    assertTrue(token.getPosition().equals(position.toString()));
    assertTrue(token.toString().equals("test.trs:3:9: counter (IDENTIFIER)"));
  }

  @Test
  public void testEof() {
    ParsePosition position = new ParsePosition("test.trs", 4, 7);
    Token token = Token.eofToken(position);
    assertTrue(token.isEof());
    assertTrue(token.getName().equals("EOF"));
    assertTrue(token.getText().equals(""));
    assertTrue(token.getPosition().equals(position.toString()));
    assertTrue(token.toString().equals("test.trs:4:7:  (EOF)"));
  }

  @Test
  public void testBefore() {
    ParsePosition pos1 = new ParsePosition("test.trs", 1, 2);
    ParsePosition pos2 = new ParsePosition("test.trs", 1, 2);
    ParsePosition pos3 = new ParsePosition("test.trs", 2, 1);
    Token tok1 = new Token(pos1, "IDENTIFIER", "a");
    Token tok2 = new Token(pos2, "IDENTIFIER", "a");
    Token tok3 = new Token(pos3, "IDENTIFIER", "a");
    assertFalse(tok1.before(tok2));
    assertTrue(tok1.before(tok3));
  }

  @Test
  public void testUpdate() {
    ParsePosition position = new ParsePosition("test.trs", 3, 9);
    Token tok1 = new Token(position, "IDENTIFIER", "counter");
    Token tok2 = tok1.updateText("tree");
    assertTrue(tok1.toString().equals("test.trs:3:9: counter (IDENTIFIER)"));
    assertTrue(tok2.toString().equals("test.trs:3:9: tree (IDENTIFIER)"));
  }
}

