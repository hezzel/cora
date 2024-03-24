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
    collector.addError("AAA");
    collector.addError("BBB");
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals("AAA\nBBB\n"));
  }

  @Test
  public void testMaxMessages() {
    ErrorCollector collector = new ErrorCollector(2);
    collector.addError("AAA");
    collector.addError("BBB");
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals("AAA\nBBB\n"));
  }

  @Test
  public void testAddBefore() {
    ErrorCollector collector = new ErrorCollector(5);
    collector.addError("AAA");
    collector.addError("BBB");
    collector.addErrorBefore(1, "CCC");
    assertTrue(collector.queryErrorCount() == 3);
    collector.addErrorBefore(-1, "DDD");
    collector.addErrorBefore(5, "EEE");
    assertTrue(collector.queryErrorCount() == 5);
    assertTrue(collector.queryCollectedMessages().equals("DDD\nAAA\nCCC\nBBB\nEEE\n"));
    collector.addErrorBefore(2, "FFF");
    assertTrue(collector.queryErrorCount() == 5);
    assertTrue(collector.queryCollectedMessages().equals("DDD\nAAA\nCCC\nBBB\nEEE\n"));
  }

  @Test
  public void testTooManyMessages() {
    ErrorCollector collector = new ErrorCollector(2);
    collector.addError("AAA");
    collector.addError("BBB");
    collector.addError("CCC");
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals("AAA\nBBB\n"));
  }
}

