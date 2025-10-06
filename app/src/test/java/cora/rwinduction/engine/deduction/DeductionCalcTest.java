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
import charlie.terms.position.PositionFormatException;
import charlie.terms.replaceable.MutableRenaming;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class DeductionCalcTest {
  private TRS trs = CoraInputReader.readTrsFromString(
    "iter :: Int -> Int -> Int -> Int\n" +
    "iter(x, a, z) -> z | a > x\n" +
    "iter(x, a, b) -> iter(x, a+1, b+a) | a <= x\n");

  public PartialProof setupProof() {
    return new PartialProof(trs,
      EquationParser.parseEquationList(
        "iter(x + y, x * 2, x / y) -><- iter(- y, u + 12, 17) | a = x + y ∧ x / y = u ∧ -y = z ; " +
        "iter(1 + (2 + 3), x * y + z, x + y) -><- x + y| x ≥ 0 ∧ u = x * y ;"
        , trs),
      lst -> new MutableRenaming(trs.queryFunctionSymbolNames()));
  }

  @Test
  public void testImmediateStep() throws PositionFormatException {
    PartialProof pp = setupProof();
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.parse("l1.2.ε");
    DeductionCalc step = DeductionCalc.createStep(pp, o, List.of(pos));
    assertTrue(step.commandDescription().equals("calc l1.2"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals("We use CALC at position l1.2.\n\n"));
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (• , iter(1 + 5, x * y + z, x + y) ≈ x + y | x ≥ 0 ∧ u = x * y , •)"));
  }

  @Test
  public void testKnownCalculation() throws PositionFormatException {
    PartialProof pp = setupProof();
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.parse("2.1");
    DeductionCalc step = DeductionCalc.createStep(pp, o, List.of(pos));
    assertTrue(step.commandDescription().equals("calc l2.1"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals("We use CALC at position l2.1.\n\n"));
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (• , iter(1 + (2 + 3), u + z, x + y) ≈ x + y | x ≥ 0 ∧ u = x * y , •)"));
  }

  @Test
  public void testMultipleKnownCalculations() throws PositionFormatException {
    PartialProof pp = setupProof();
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> o = Optional.of(module);
    // skip to E1
    pp.addProofStep(pp.getProofState().deleteTopEquation(), DeductionDelete.createStep(pp,o));
    DeductionCalc step = DeductionCalc.createStep(pp,o,List.of(
      EquationPosition.parse("l1"),
      EquationPosition.parse("l3"),
      EquationPosition.parse("r1")));
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (• , iter(a, x * 2, u) ≈ iter(z, u + 12, 17) | a = x + y ∧ x / y = u ∧ -y = z , •)"));
    step.explain(module);
    assertTrue(module.toString().equals("We use CALC at positions l1, l3 and r1.\n\n"));
  }

  @Test
  public void testUnknownCalculation() throws PositionFormatException {
    PartialProof pp = setupProof();
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.parse("l3");
    DeductionCalc step = DeductionCalc.createStep(pp, o, List.of(pos));
    assertTrue(step.commandDescription().equals("calc l3"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals("We use ALTER to add i1 = x + y to the constraint, " +
      "and then use CALC at position l3.\n\n"));
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (• , iter(1 + (2 + 3), x * y + z, i1) ≈ x + y | x ≥ 0 ∧ u = x * y ∧ i1 = x + y , •)"));
  }

  @Test
  public void testMultipleUnknownCalculation() throws PositionFormatException {
    PartialProof pp = setupProof();
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos1 = EquationPosition.parse("l3");
    EquationPosition pos2 = EquationPosition.parse("r");
    DeductionCalc step = DeductionCalc.createStep(pp, o, List.of(pos1, pos2));
    assertTrue(step.commandDescription().equals("calc l3 r"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals("We use ALTER to add i1 = x + y to the constraint, " +
      "and then use CALC at positions l3 and r.\n\n"));
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (• , iter(1 + (2 + 3), x * y + z, i1) ≈ i1 | x ≥ 0 ∧ u = x * y ∧ i1 = x + y , •)"));
  }

  @Test
  public void testBiggerKnownCalculation() throws PositionFormatException {
    PartialProof pp = setupProof();
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.parse("l1");
    DeductionCalc step = DeductionCalc.createStep(pp, o, List.of(pos));
    assertTrue(step.commandDescription().equals("calc l1"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals("We use CALC at position l1.\n\n"));
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (• , iter(6, x * y + z, x + y) ≈ x + y | x ≥ 0 ∧ u = x * y , •)"));
  }

  @Test
  public void testBiggerUnknownCalculation() throws PositionFormatException {
    PartialProof pp = setupProof();
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.parse("l2");
    DeductionCalc step = DeductionCalc.createStep(pp, o, List.of(pos));
    step.explain(module);
    assertTrue(module.toString().equals("We use ALTER to add a1 = x * y + z to the constraint, " +
      "and then use CALC at position l2.\n\n"));
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (• , iter(1 + (2 + 3), a1, x + y) ≈ x + y | x ≥ 0 ∧ u = x * y ∧ a1 = x * y + z , •)"));
  }

  @Test
  public void testMultiStepRightOrder() throws PositionFormatException {
    PartialProof pp = setupProof();
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.parse("l2");
    DeductionCalc step = DeductionCalc.createStep(pp, o, List.of(
      EquationPosition.parse("l1.2"), EquationPosition.parse("l2.1"),
      EquationPosition.parse("l2"), EquationPosition.parse("l1")));
    step.explain(module);
    assertTrue(module.toString().equals("We use ALTER to add a1 = u + z to the constraint, and " +
      "then use CALC at positions l1.2, l2.1, l2 and l1.\n\n"));
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (• , iter(6, a1, x + y) ≈ x + y | x ≥ 0 ∧ u = x * y ∧ a1 = u + z , •)"));
  }

  @Test
  public void testMultistepWrongOrder() throws PositionFormatException {
    PartialProof pp = setupProof();
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> o = Optional.of(module);
    assertTrue(DeductionCalc.createStep(pp, o, List.of(EquationPosition.parse("l1"),
      EquationPosition.parse("l1.2"))) == null);
    assertTrue(module.toString().equals(
      "Subterm at position l1.2 has already been calculated away!\n\n"));
  }

  @Test
  public void testNaming() throws PositionFormatException {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> o = Optional.of(module);
    PartialProof proof = new PartialProof(trs,
      EquationParser.parseEquationList("iter(x + y, x * 2, z + x / y) = " +
                                       "iter(- y, a - 1, z + 17)", trs),
      lst -> module.generateUniqueNaming(lst));
    DeductionCalc step = DeductionCalc.createStep(proof, o, List.of(
      EquationPosition.parse("l1"), EquationPosition.parse("l2"), EquationPosition.parse("l3"),
      EquationPosition.parse("r1"), EquationPosition.parse("r2"), EquationPosition.parse("r3")));
    assertTrue(step.verifyAndExecute(proof, o));
    assertTrue(proof.getProofState().getTopEquation().toString().equals(
      "E2: (• , iter(x1, x2, i1) ≈ iter(y1, a1, z1) | x1 = x + y ∧ x2 = x * 2 ∧ " +
      "i1 = z + x / y ∧ y1 = -y ∧ a1 = a - 1 ∧ z1 = z + 17 , •)"));
  }
}

