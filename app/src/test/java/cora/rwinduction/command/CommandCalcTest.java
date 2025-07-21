/**************************************************************************************************
 Copyright 2024-2025 Cynthia Kop

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
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.engine.DeductionStep;
import cora.rwinduction.parser.CommandParsingStatus;
import cora.rwinduction.parser.EquationParser;

class CommandCalcTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString("f :: Int -> Int -> A");
  }

  private DeductionStep createStep(OutputModule module, String str) {
    CommandCalc cmd = new CommandCalc();
    TRS trs = setupTRS();
    PartialProof proof = new PartialProof(trs,
      EquationParser.parseEquationList("f(x + 1, x + 3 * 7) -><- f(x-4,2)| true", trs),
      lst -> module.generateUniqueNaming(lst));
    cmd.storeContext(proof, module);
    CommandParsingStatus status = new CommandParsingStatus(str);
    status.nextWord(); // :rules
    return cmd.createStep(status);
  }

  @Test
  public void testTwoLegalPositions() {
    OutputModule module = OutputModule.createUnitTestModule();
    DeductionStep step = createStep(module, "calc L1 R1");
    step.explain(module);
    assertTrue(module.toString().equals("We use ALTER to add x1 = x + 1 ∧ x2 = x - 4 to the " +
      "constraint, and then use CALC at positions L1 and R1.\n\n"));
  }

  @Test
  public void testBadInvocation() {
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(createStep(module, "calc L1 LR R1") == null);
    assertTrue(module.toString().equals("Illegal position LR: 1:0: Parser exception on input " +
      "[R]: position index should be an integer\n\n"));
  }

  @Test
  public void testUnsuitablePositions() {
    OutputModule module = OutputModule.createUnitTestModule();
    // R4 does not exist
    assertTrue(createStep(module, "calc L1 R4") == null);
    // L2.1 exists, but is not calculatable
    assertTrue(createStep(module, "calc L2.1 R1") == null);

    assertTrue(module.toString().equals("No such position: R4.\n\nThe subterm x at " +
      "position L2.1 is not calculatable: it should be a first-order theory term.\n\n"));
  }
}

