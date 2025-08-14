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

package cora.rwinduction.engine.deduction;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;
import java.util.Set;
import java.util.Optional;

import charlie.util.FixedList;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class DeductionSkipTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "sum1 :: Int -> Int\n" +
      "sum1(x) -> 0 | x <= 0\n" +
      "sum1(x) -> x + sum1(x-1) | x > 0\n" +
      "sum2 :: Int -> Int\n" +
      "sum2(x) -> iter(x, 0, 0)\n" +
      "iter :: Int -> Int -> Int -> Int\n" +
      "iter(x, i, z) -> z | i > x\n" +
      "iter(x, i, z) -> iter(x, i+1, z+i) | i <= x\n");
  }

  public PartialProof setupProof(OutputModule module, int count) {
    TRS trs = setupTRS();
    return new PartialProof(trs,
      count == 0 ? FixedList.of() :
      EquationParser.parseEquationList("" +
        (count > 0 ? "sum1(x) = sum2(x) | x ≥ 0 ; " : "") +
        (count > 1 ? "iter(x, i, z) = iter(x, 1+i, i+z+0) | i < x ; " : "") +
        (count > 2 ? "sum2(x+0) = 0 + sum1(x)" : ""), trs),
      lst -> module.generateUniqueNaming(lst));
  }

  @Test
  public void testSkipProperly() {
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    PartialProof pp = setupProof(module, 3);
    DeductionSkip step = DeductionSkip.createStep(pp, o);
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getEquations().size() == 3);
    assertTrue(pp.getProofState().getLastUsedIndex() == 3);
    assertTrue(pp.getCommandHistory().size() == 1);
    assertTrue(pp.getCommandHistory().get(0).equals("skip"));
    assertTrue(pp.getProofState().getEquations().get(0).getIndex() == 3);
    assertTrue(pp.getProofState().getEquations().get(1).getIndex() == 1);
    assertTrue(pp.getProofState().getEquations().get(2).getIndex() == 2);
    assertTrue(module.toString().equals(""));
  }

  @Test
  public void testSkipEmpty() {
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    PartialProof pp = setupProof(module, 0);
    assertTrue(DeductionSkip.createStep(pp, o) == null);
    assertTrue(module.toString().equals(
      "The SKIP rule cannot be applied, since there are no equations.\n\n"));
  }

  @Test
  public void testSkipJustOne() {
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    PartialProof pp = setupProof(module, 1);
    DeductionSkip step = DeductionSkip.createStep(pp, o);
    assertFalse(step.verifyAndExecute(pp, o));
    assertTrue(module.toString().equals(
      "The SKIP rule cannot be applied, since there is only one equation.\n\n"));
  }
}

