/**************************************************************************************************
 Copyright 2025 Cynthia Kop

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

import charlie.terms.replaceable.MutableRenaming;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;
import cora.rwinduction.engine.deduction.DeductionCalcAll.Side;

class DeductionCalcAllTest {
  private TRS trs = CoraInputReader.readTrsFromString(
    "iter :: Int -> Int -> Int -> Int\n" +
    "iter(x, i, z) -> z | i > x\n" +
    "iter(x, i, z) -> iter(x, i+1, z+i) | i <= x\n");

  public PartialProof setupProof(String eqs) {
    return new PartialProof(trs,
      EquationParser.parseEquationList(eqs, trs),
      lst -> new MutableRenaming(trs.queryFunctionSymbolNames()));
  }

  @Test
  public void testImmediateSteps() {
    PartialProof pp = setupProof("iter(1 + (2 + 3), 5, 17 - 5) = iter(1, 2 + 3, x)");
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> o = Optional.of(module);
    DeductionCalcAll step = DeductionCalcAll.createStep(pp, o, Side.Both);
    assertTrue(step.commandDescription().equals("calc"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals(
      "We use CALC at all 3 positions where it is possible.\n\n"));
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , iter(6, 5, 12) ≈ iter(1, 5, x) , •)"));
  }

  @Test
  public void testKnownSteps() {
    PartialProof pp = setupProof("iter(x + y, a, x / y) -><- iter(- y, u + 12, 17) | " +
      "a = x + y ∧ x / y = u ∧ -y = z");
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> o = Optional.of(module);
    DeductionCalcAll step = DeductionCalcAll.createStep(pp, o, Side.Left);
    assertTrue(step.commandDescription().equals("calc left"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals("We use CALC at all 2 positions in the left-hand side " +
      "of the equation where it is possible.\n\n"));
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , iter(a, a, u) ≈ iter(-y, u + 12, 17) | a = x + y ∧ x / y = u ∧ -y = z , •)"));
  }

  @Test
  public void testUnknownSteps() {
    PartialProof pp = setupProof("iter(1 + 2, x, y) -><- iter(- y, u + 12, x / y) | y > 0");
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> o = Optional.of(module);
    DeductionCalcAll step = DeductionCalcAll.createStep(pp, o, Side.Right);
    assertTrue(step.commandDescription().equals("calc right"));
    step.explain(module);
    assertTrue(module.toString().equals("We use CALC at all 3 positions in the right-hand side " +
      "of the equation where it is possible.\n\n"));
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , iter(1 + 2, x, y) ≈ iter(y1, u1, z1) | " +
      "y > 0 ∧ y1 = -y ∧ u1 = u + 12 ∧ z1 = x / y , •)"));
  }

  @Test
  public void testMixedSteps() {
    PartialProof pp = setupProof("iter(x + y, x * (1 + (2 - 3)), x / y) -><- " +
      "iter(17, - y, 9 + u + 12) | a = x + y ∧ x / y = u ∧ -y = z");
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> o = Optional.of(module);
    DeductionCalcAll step = DeductionCalcAll.createStep(pp, o, Side.Both);
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , iter(a, x1, u) ≈ iter(17, z, u1) | a = x + y ∧ x / y = u ∧ -y = z ∧ " +
      "x1 = x * (1 + (2 - 3)) ∧ u1 = 9 + u + 12 , •)"));
  }

  @Test
  public void testSingleReplacement() {
    PartialProof pp = setupProof("iter(1 + 2, x, y) -><- iter(- y, u + 12, x / y) | y > 0");
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> o = Optional.of(module);
    DeductionCalcAll step = DeductionCalcAll.createStep(pp, o, Side.Left);
    assertTrue(step.commandDescription().equals("calc left"));
    step.explain(module);
    assertTrue(module.toString().equals("We use CALC at the only position in the left-hand side " +
      "of the equation where it is possible.\n\n"));
  }

  @Test
  public void testNothingToCalculate() {
    PartialProof pp = setupProof("iter(1, x, y) -><- iter(-2, u, iter(x, y, z)) | y > 0");
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> o = Optional.of(module);
    assertTrue(DeductionCalcAll.createStep(pp, o, Side.Left) == null);
    assertTrue(module.toString().equals("There are no calculatable subterms.\n\n"));
  }
}

