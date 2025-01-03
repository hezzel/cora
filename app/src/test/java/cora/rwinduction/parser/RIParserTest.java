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

import charlie.parser.lib.ParsingStatus;

class RIParserTest {
  @Test
  public void testTokensOnTheirOwn() {
    ParsingStatus status = RIParser.createStatus("≈ -><- := ;");
    assertTrue(status.nextToken().toString().equals("1:1: ≈ (APPROX)"));
    assertTrue(status.nextToken().toString().equals("1:3: -><- (APPROX)"));
    assertTrue(status.nextToken().toString().equals("1:8: := (ASSIGN)"));
    assertTrue(status.nextToken().toString().equals("1:11: ; (SEPARATOR)"));
    assertTrue(status.nextToken().isEof());
  }

  @Test
  public void testTokensInsideIdentifiers() {
    ParsingStatus status = RIParser.createStatus(
      "aa-><-:=bb a≈b ≈a b≈ a;c ;a a; a;b≈c a≈b;c");
    assertTrue(status.nextToken().toString().equals("1:1: aa (IDENTIFIER)"));
    assertTrue(status.nextToken().toString().equals("1:3: -><- (APPROX)"));
    assertTrue(status.nextToken().toString().equals("1:7: := (ASSIGN)"));
    assertTrue(status.nextToken().toString().equals("1:9: bb (IDENTIFIER)"));
    assertTrue(status.nextToken().toString().equals("1:12: a (IDENTIFIER)"));
    assertTrue(status.nextToken().toString().equals("1:13: ≈ (APPROX)"));
    assertTrue(status.nextToken().toString().equals("1:14: b (IDENTIFIER)"));
    assertTrue(status.nextToken().toString().equals("1:16: ≈ (APPROX)"));
    assertTrue(status.nextToken().toString().equals("1:17: a (IDENTIFIER)"));
    assertTrue(status.nextToken().toString().equals("1:19: b (IDENTIFIER)"));
    assertTrue(status.nextToken().toString().equals("1:20: ≈ (APPROX)"));
    assertTrue(status.nextToken().toString().equals("1:22: a (IDENTIFIER)"));
    assertTrue(status.nextToken().toString().equals("1:23: ; (SEPARATOR)"));
    assertTrue(status.nextToken().toString().equals("1:24: c (IDENTIFIER)"));
    assertTrue(status.nextToken().toString().equals("1:26: ; (SEPARATOR)"));
    assertTrue(status.nextToken().toString().equals("1:27: a (IDENTIFIER)"));
    assertTrue(status.nextToken().toString().equals("1:29: a (IDENTIFIER)"));
    assertTrue(status.nextToken().toString().equals("1:30: ; (SEPARATOR)"));
    assertTrue(status.nextToken().toString().equals("1:32: a (IDENTIFIER)"));
    assertTrue(status.nextToken().toString().equals("1:33: ; (SEPARATOR)"));
    assertTrue(status.nextToken().toString().equals("1:34: b (IDENTIFIER)"));
    assertTrue(status.nextToken().toString().equals("1:35: ≈ (APPROX)"));
    assertTrue(status.nextToken().toString().equals("1:36: c (IDENTIFIER)"));
    assertTrue(status.nextToken().toString().equals("1:38: a (IDENTIFIER)"));
    assertTrue(status.nextToken().toString().equals("1:39: ≈ (APPROX)"));
    assertTrue(status.nextToken().toString().equals("1:40: b (IDENTIFIER)"));
    assertTrue(status.nextToken().toString().equals("1:41: ; (SEPARATOR)"));
    assertTrue(status.nextToken().toString().equals("1:42: c (IDENTIFIER)"));
    assertTrue(status.nextToken().isEof());
  }
}
