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

package cora.parser;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import java.util.ArrayList;

import cora.parser.lib.Token;
import cora.parser.lib.ErrorCollector;
import cora.parser.lib.ParsingStatus;
import cora.parser.Parser.*;
import cora.parser.InfixManager.OperatorData;

public class InfixManagerTest {
  private ParserTerm convert(String desc, InfixManager manager, ErrorCollector collector) {
    ParsingStatus status;
    if (collector == null) status = new ParsingStatus(OCocoTokenData.getStringLexer(desc), 12);
    else status = new ParsingStatus(OCocoTokenData.getStringLexer(desc), collector);
    ArrayList<ParserTerm> terms = new ArrayList<ParserTerm>();
    ArrayList<OperatorData> operators = new ArrayList<OperatorData>();
    while (true) {
      Token term = status.nextToken();
      Token op = status.nextToken();
      terms.add(new Identifier(term, term.getText()));
      if (op.isEof()) break;
      operators.add(new OperatorData(op, op.getText()));
    }
    ParserTerm ret = manager.convertChain(terms, operators, status);
    if (collector == null) status.throwCollectedErrors();
    return ret;
  }

  @Test
  public void testRepeatedLeftInfix() {
    InfixManager manager = new InfixManager();
    manager.addGroup(manager.ASSOC_LEFT, 10, "+");
    ParserTerm t = convert("x1 + x2 + x3 + x4", manager, null);
    assertTrue(t.toString().equals("@(+, [@(+, [@(+, [x1, x2]), x3]), x4])"));
  }

  @Test
  public void testRepeatedRightInfix() {
    InfixManager manager = new InfixManager();
    manager.addGroup(manager.ASSOC_RIGHT, 10, "+");
    ParserTerm t = convert("x1 + x2 + x3 + x4", manager, null);
    assertTrue(t.toString().equals("@(+, [x1, @(+, [x2, @(+, [x3, x4])])])"));
  }

  @Test
  public void testRepeatedNoInfix() {
    InfixManager manager = new InfixManager();
    ErrorCollector collector = new ErrorCollector();
    manager.addGroup(manager.ASSOC_NONE, 10, "+");
    ParserTerm t = convert("x1 + x2 + x3 + x4", manager, collector);
    assertTrue(t.toString().equals("@(+, [ERR(@(+, [ERR(@(+, [x1, x2])), x3])), x4])"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:9: Illegal infix sequence: operator + is not associative, so " +
        "cannot be used after + (at position 1:4).\n" +
      "1:14: Illegal infix sequence: operator + is not associative, so " +
        "cannot be used after + (at position 1:9).\n"));
  }

  @Test
  public void testLowToHighPriorityLeft() {
    InfixManager manager = new InfixManager();
    manager.addGroup(manager.ASSOC_LEFT, 1, "+", "-");
    manager.addGroup(manager.ASSOC_LEFT, 2, "*");
    manager.addGroup(manager.ASSOC_LEFT, 3, "^");
    ParserTerm t = convert("x1 + x2 * x3 ^ x4 * x5 - x6", manager, null);
    assertTrue(t.toString().equals(
      "@(-, [@(+, [x1, @(*, [@(*, [x2, @(^, [x3, x4])]), x5])]), x6])"));
  }

  @Test
  public void testLowToHighPriorityRight() {
    InfixManager manager = new InfixManager();
    manager.addGroup(manager.ASSOC_RIGHT, 1, "+", "-");
    manager.addGroup(manager.ASSOC_RIGHT, 2, "*");
    manager.addGroup(manager.ASSOC_RIGHT, 3, "^");
    ParserTerm t = convert("x1 + x2 * x3 ^ x4 * x5 - x6", manager, null);
    assertTrue(t.toString().equals(
      "@(+, [x1, @(-, [@(*, [x2, @(*, [@(^, [x3, x4]), x5])]), x6])])"));
  }

  @Test
  public void testAmbiguityLeft() {
    InfixManager manager = new InfixManager();
    manager.addGroup(manager.ASSOC_LEFT, 1, "&");
    manager.addGroup(manager.ASSOC_LEFT, 1, "|");
    ErrorCollector collector = new ErrorCollector();
    ParserTerm t = convert("x1 & x2 & x3 | x4 | x5", manager, collector);
    assertTrue(t.toString().equals("@(|, [@(|, [ERR(@(&, [@(&, [x1, x2]), x3])), x4]), x5])"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:14: Ambiguous infix sequence: operators & (at position 1:9) and | have the same " +
      "precedence, but are not in the same group.  Please use brackets to disambiguate.\n"));
  }

  @Test
  public void testAmbiguityRight() {
    InfixManager manager = new InfixManager();
    manager.addGroup(manager.ASSOC_RIGHT, 1, "&");
    manager.addGroup(manager.ASSOC_RIGHT, 1, "|");
    ErrorCollector collector = new ErrorCollector();
    ParserTerm t = convert("x1 & x2 & x3 | x4 | x5", manager, collector);
    assertTrue(t.toString().equals(
      "@(|, [ERR(@(&, [x1, ERR(@(&, [x2, x3]))])), @(|, [x4, x5])])"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:14: Ambiguous infix sequence: operators & (at position 1:9) and | have the same " +
      "precedence, but are not in the same group.  Please use brackets to disambiguate.\n"));
  }

  @Test
  public void testAmbiguityLeftRight() {
    InfixManager manager = new InfixManager();
    manager.addGroup(manager.ASSOC_LEFT, 1, "&");
    manager.addGroup(manager.ASSOC_RIGHT, 1, "|");
    ErrorCollector collector = new ErrorCollector();
    ParserTerm t = convert("x1 & x2 & x3 | x4 | x5", manager, collector);
    assertTrue(t.toString().equals(
      "@(|, [ERR(@(&, [@(&, [x1, x2]), x3])), @(|, [x4, x5])])"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:14: Ambiguous infix sequence: operators & (at position 1:9) and | have the same " +
      "precedence, but are not in the same group.  Please use brackets to disambiguate.\n"));
  }

  @Test
  public void testAmbiguityRightLeft() {
    InfixManager manager = new InfixManager();
    manager.addGroup(manager.ASSOC_RIGHT, 1, "&");
    manager.addGroup(manager.ASSOC_LEFT, 1, "|");
    ErrorCollector collector = new ErrorCollector();
    ParserTerm t = convert("x1 & x2 & x3 | x4 | x5", manager, collector);
    assertTrue(t.toString().equals(
      "@(|, [@(|, [ERR(@(&, [x1, ERR(@(&, [x2, x3]))])), x4]), x5])"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:14: Ambiguous infix sequence: operators & (at position 1:9) and | have the same " +
      "precedence, but are not in the same group.  Please use brackets to disambiguate.\n"));
  }
}

