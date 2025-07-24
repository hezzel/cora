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

public class ErrorCollectorTest {
  @Test
  public void testBasics() {
    ErrorCollector collector = new ErrorCollector(3);
    collector.addError(new ParsingErrorMessage(null, "AAA"));
    collector.addError(new ParsingErrorMessage(null, "BBB"));
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.toString().equals("AAA\nBBB\n"));
  }

  @Test
  public void testMaxMessages() {
    ErrorCollector collector = new ErrorCollector(2);
    collector.addError(new ParsingErrorMessage(null, "AAA"));
    collector.addError(new ParsingErrorMessage(null, "BBB"));
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.toString().equals("AAA\nBBB\n"));
  }

  @Test
  public void testAddBefore() {
    ErrorCollector collector = new ErrorCollector(5);
    Token token = new Token(new ParsePosition(1, 3), "NAME", "x");
    collector.addError(new ParsingErrorMessage(token, "AAA"));
    collector.addError(new ParsingErrorMessage(null, "BBB"));
    collector.addErrorBefore(1, new ParsingErrorMessage(null, "CCC"));
    assertTrue(collector.queryErrorCount() == 3);
    token = new Token(new ParsePosition(2, 7), "", "");
    collector.addErrorBefore(-1, new ParsingErrorMessage(token, "DDD"));
    collector.addErrorBefore(5, new ParsingErrorMessage(null, "EEE"));
    assertTrue(collector.queryErrorCount() == 5);
    assertTrue(collector.toString().equals("2:7: DDD\n1:3: AAA\nCCC\nBBB\nEEE\n"));
    collector.addErrorBefore(2, new ParsingErrorMessage(null, "FFF"));
    assertTrue(collector.queryErrorCount() == 5);
    assertTrue(collector.toString().equals("2:7: DDD\n1:3: AAA\nCCC\nBBB\nEEE\n"));
  }

  @Test
  public void testTooManyMessages() {
    ErrorCollector collector = new ErrorCollector(2);
    collector.addError(new ParsingErrorMessage(null, "AAA"));
    collector.addError(new ParsingErrorMessage(null, "BBB"));
    collector.addError(new ParsingErrorMessage(null, "CCC"));
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.toString().equals("AAA\nBBB\n"));
  }
}

