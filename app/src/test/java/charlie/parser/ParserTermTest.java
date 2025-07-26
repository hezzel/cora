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

import charlie.util.FixedList;
import charlie.types.TypeFactory;
import charlie.parser.lib.Token;
import charlie.parser.lib.ParsingStatus;
import charlie.parser.Parser.*;

public class ParserTermTest {
  /** We cannot generate a token directly, but we can ask the ParsingStatus to give us one. */
  private Token makeToken() {
    ParsingStatus status = new ParsingStatus(OCocoTokenData.getStringLexer("x"), 1);
    return status.nextToken();
  }

  @Test
  public void testIdentifierErrors() {
    Token t = makeToken();
    ParserTerm a = new Identifier(t, "x");
    ParserTerm b = new PErr(a);
    assertFalse(a.hasErrors());
    assertTrue(b.hasErrors());
  }

  @Test
  public void testLambdaErrors() {
    Token t = makeToken();
    ParserTerm a = new Identifier(t, "x");
    ParserTerm b = new PErr(a);
    ParserTerm c = new Lambda(t, "x", TypeFactory.intSort, a);
    ParserTerm d = new Lambda(t, "x", TypeFactory.intSort, b);
    assertFalse(c.hasErrors());
    assertTrue(d.hasErrors());
  }

  @Test
  public void testArgumentCombinedErrors() {
    Token t = makeToken();
    ParserTerm a = new Identifier(t, "x");
    ParserTerm b = new Lambda(t, "x", TypeFactory.intSort, a);
    ParserTerm c = new Identifier(t, "aa");
    ParserTerm h = new Identifier(t, "f");
    FixedList<ParserTerm> goodlst = FixedList.of(a, c);
    FixedList<ParserTerm> badlst1 = FixedList.of(a, new PErr(c));
    FixedList<ParserTerm> badlst2 = FixedList.of(new PErr(a), c);
    FixedList<ParserTerm> badlst3 = FixedList.of(new PErr(a), new PErr(c));

    ParserTerm d1 = new Meta(t, "Z", goodlst);
    ParserTerm d2 = new Meta(t, "Z", badlst1);
    ParserTerm d3 = new Meta(t, "Z", badlst2);
    ParserTerm d4 = new Meta(t, "Z", badlst3);
    ParserTerm e1 = new Application(t, h, goodlst);
    ParserTerm e2 = new Application(t, h, badlst1);
    ParserTerm e3 = new Application(t, h, badlst2);
    ParserTerm e4 = new Application(t, new PErr(h), goodlst);
    ParserTerm f1 = new Tup(t, goodlst);
    ParserTerm f2 = new Tup(t, badlst1);
    ParserTerm f3 = new Tup(t, badlst2);
    assertFalse(d1.hasErrors());
    assertTrue(d2.hasErrors());
    assertTrue(d3.hasErrors());
    assertTrue(d4.hasErrors());
    assertFalse(e1.hasErrors());
    assertTrue(e2.hasErrors());
    assertTrue(e3.hasErrors());
    assertTrue(e4.hasErrors());
    assertFalse(f1.hasErrors());
    assertTrue(f2.hasErrors());
    assertTrue(f3.hasErrors());
  }
}

