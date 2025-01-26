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

import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.engine.deduction.DeductionDelete;
import cora.rwinduction.engine.deduction.DeductionCase;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.parser.CommandParsingStatus;

class CommandCaseTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "return :: Int -> result\n" +
      "error :: result\n" +
      "sum1 :: Int -> result\n" +
      "sum1(x) -> return(0) | x <= 0\n" +
      "sum1(x) -> add(x,sum1(x-1)) | x > 0\n" +
      "add :: Int -> result -> result\n" +
      "add(x, return(y)) -> return(x+y)\n" +
      "add(x, error) -> error\n" +
      "sum2 :: Int -> result\n" +
      "sum2(x) -> iter(x, 0, 0)\n" +
      "iter :: Int -> Int -> Int -> result\n" +
      "iter(x, i, z) -> return(z) | i > x\n" +
      "iter(x, i, z) -> iter(x, i+1, z+i) | i <= x\n");
  }

  private TRS trs = setupTRS();

  private Optional<DeductionCase> createStep(OutputModule module, String str) {
    CommandCase cmd = new CommandCase();
    PartialProof proof = new PartialProof(trs, EquationParser.parseEquationList(
      "iter(x, i, z) = add(x, y) | x > 0", trs), lst -> module.generateUniqueNaming(lst));
    cmd.storeContext(proof, module);
    CommandParsingStatus status = new CommandParsingStatus(str);
    status.nextWord(); // case
    return cmd.createStep(status);
  }

  @Test
  public void testGoodStepWithTerm() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<DeductionCase> step = createStep(module, "case i - x");
    assertTrue(step.get().toString().equals("case i - x"));
  }

  @Test
  public void testGoodStepWithVariable() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<DeductionCase> step = createStep(module, "case y");
    assertTrue(step.get().toString().equals("case y"));
  }

  @Test
  public void testStepContainingFreshVariable() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<DeductionCase> step = createStep(module, "case i - u > 0");
    assertTrue(step.get().toString().equals("case i - u > 0"));
    assertFalse(step.get().verify(Optional.of(module)));
    assertTrue(module.toString().equals("Unknown variable in case term: \"i - u > 0\".\n\n"));
  }

  @Test
  public void testStepWithFreshVariable() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<DeductionCase> step = createStep(module, "case u");
    assertTrue(step.isEmpty());
    assertTrue(module.toString().equals("Unknown variable: u\n\n"));
  }

  @Test
  public void testStepContainingTypeError() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<DeductionCase> step = createStep(module, "case i - y > 0");
    assertTrue(step.isEmpty());
    assertTrue(module.toString().equals("Parsing error at position 10: Expected term " +
      "of type Int, but got variable y which has type result.\n\n"));
  }

  @Test
  public void testStepWithoutArguments() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<DeductionCase> step = createStep(module, "case");
    assertTrue(step.isEmpty());
    assertTrue(module.toString().equals("Case should be invoked with at least one argument.\n\n"));
  }

  @Test
  public void testStepMultipleTerms() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<DeductionCase> step = createStep(module, "case x  i > 0");
    assertTrue(step.isEmpty());
    assertTrue(module.toString().equals(
      "Unexpected argument at position 9: expected end of command.\n\n"));
  }
}

