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

import charlie.util.FixedList;
import charlie.terms.TheoryFactory;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.rwinduction.engine.EquationContext;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.engine.deduction.DeductionSimplify;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.parser.CommandParsingStatus;

class CommandSimplifyTest {
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

  private Optional<DeductionSimplify> createStep(OutputModule module, String str) {
    CommandSimplify cmd = new CommandSimplify();
    TRS trs = setupTRS();
    EquationContext ec =
      EquationParser.parseEquationData("sum1(z) = add(y,sum2(z)) | z ≥ 0 ∧ y < 0", trs, 1);
    PartialProof proof = new PartialProof(trs, FixedList.of(ec), module.queryTermPrinter());
    cmd.storeContext(proof, module);
    CommandParsingStatus status = new CommandParsingStatus(str);
    status.nextWord(); // simplify
    return cmd.createStep(status);
  }

  private boolean execute(OutputModule module, String str) {
    CommandSimplify cmd = new CommandSimplify();
    TRS trs = setupTRS();
    EquationContext ec =
      EquationParser.parseEquationData("sum1(z) = add(y,sum2(z)) | z ≥ 0 ∧ y < 0", trs, 1);
    PartialProof proof = new PartialProof(trs, FixedList.of(ec), module.queryTermPrinter());
    cmd.storeContext(proof, module);
    CommandParsingStatus status = new CommandParsingStatus(str);
    status.nextWord(); // simplify
    return cmd.execute(status);
  }

  @Test
  public void testGoodStepWithoutSubstitution() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    DeductionSimplify step = createStep(module, "simplify O5 R.2").get();
    assertTrue(step.toString().equals("simplify O5 R2 with [x := z]"));
  }

  @Test
  public void testGoodStepWithSubstitution() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    DeductionSimplify step = createStep(module, "simplify O1 with [x:=z]").get();
    assertTrue(step.toString().equals("simplify O1 L with [x := z]"));
  }

  @Test
  public void testNonExistingRule() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    assertTrue(createStep(module, "simplify R19 R.2").isEmpty());
    assertTrue(module.toString().equals("No such rule: R19\n\n"));

    module.clear();
    assertFalse(execute(module, "simplify 5 R.2"));
    assertTrue(module.toString().equals("No such rule: 5\n\n"));
  }

  @Test
  public void testBadPosition() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    assertTrue(createStep(module, "simplify O5 L1.2.3.2 with [x:=1]").isEmpty());
    assertTrue(module.toString().equals("No such position: L1.2.3.2.\n\n"));
  }

  @Test
  public void testBadSubstitution() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    assertTrue(createStep(module, "simplify O5 R.2 with [x:=1]").isEmpty());
    assertTrue(module.toString().equals(
      "The rule does not apply: Variable x mapped both to 1 and to z.\n\n"));
  }

  @Test
  public void testOmitWith() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    assertFalse(execute(module, "simplify O5 R.2 [x:=z]"));
    assertTrue(module.toString().equals("Unexpected argument at position 17: expected \"with\" " +
      "or end of command, but got [x:=z].\n\n"));
  }

  @Test
  public void testTextAfterSubstitution() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    assertTrue(createStep(module, "simplify O1 with [x:=z] o").isEmpty());
    assertTrue(module.toString().equals("Unexpected argument at position 25: " +
      "expected end of command.\n\n"));
  }
}

