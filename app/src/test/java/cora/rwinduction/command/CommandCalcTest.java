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

package cora.rwinduction.command;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.Optional;
import java.util.Set;

import charlie.terms.TheoryFactory;
import charlie.parser.lib.ParsingStatus;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.engine.deduction.DeductionCalc;
import cora.rwinduction.parser.CommandParsingStatus;
import cora.rwinduction.parser.EquationParser;

class CommandCalcTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString("f :: Int -> Int -> A");
  }

  private Optional<DeductionCalc> createStep(OutputModule module, String str) {
    CommandCalc cmd = new CommandCalc();
    TRS trs = setupTRS();
    PartialProof proof = new PartialProof(trs,
      EquationParser.parseEquationList("f(x + 1, x + 3 * 7) -><- f(x-4,2)| true", trs),
      module.queryTermPrinter());
    cmd.storeContext(proof, module);
    CommandParsingStatus status = new CommandParsingStatus(str);
    status.nextWord(); // :rules
    return cmd.createStep(status);
  }

  @Test
  public void testTwoLegalPositions() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    DeductionCalc step = createStep(module, "calc L1 R1").get();
    step.explain(module);
    assertTrue(module.toString().equals("We use ALTER to add x1 = x + 1 ∧ x2 = x - 4 to the " +
      "constraint, and then use CALC at positions L1 and R1.\n\n"));
  }

  @Test
  public void testBadInvocation() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    assertTrue(createStep(module, "calc").isEmpty());
    assertTrue(createStep(module, "calc L1 LR R1").isEmpty());
    assertTrue(module.toString().equals("Calc must be given at least one argument.\n\n" +
      "Illegal position LR: 1:0: Parser exception on input [R]: position index should be an " +
      "integer\n\n"));
  }

  @Test
  public void testUnsuitablePositions() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    // R4 does not exist
    assertTrue(createStep(module, "calc L1 R4").isEmpty());
    // L2.1 exists, but is not calculatable
    assertTrue(createStep(module, "calc L2.1 R1").isEmpty());

    assertTrue(module.toString().equals("No such position: R4.\n\nThe subterm x at " +
      "position L2.1 is not calculatable: it should be a first-order theory term.\n\n"));
  }
}

