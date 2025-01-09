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

package cora.rwinduction.engine.deduction;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;
import java.util.Set;
import java.util.Optional;

import charlie.exceptions.CustomParserException;
import charlie.util.FixedList;
import charlie.terms.TermPrinter;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class DeductionCalcTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "iter :: Int -> Int -> Int -> Int\n" +
      "iter(x, i, z) -> z | i > x\n" +
      "iter(x, i, z) -> iter(x, i+1, z+i) | i <= x\n");
  }

  public PartialProof setupProof() {
    TRS trs = setupTRS();
    return new PartialProof(trs,
      EquationParser.parseEquationList(
        "iter(x + y, x * 2, x / y) -><- iter(- y, u + 12, 17) | a = x + y ∧ x / y = u ∧ -y = z ; " +
        "iter(1 + (2 + 3), x * y + z, x + y) -><- x + y| x ≥ 0 ∧ u = x * y ;"
        , trs),
      new TermPrinter(Set.of()));
  }

  @Test
  public void testImmediateStep() throws CustomParserException {
    PartialProof pp = setupProof();
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.parse("L1.2.ε");
    DeductionCalc step = DeductionCalc.createStep(pp, o, List.of(pos)).get();
    assertTrue(step.commandDescription(null).equals("calc L1.2"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals("We use CALC at position L1.2.\n\n"));
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (• , iter(1 + 5, x * y + z, x + y) ≈ x + y | x ≥ 0 ∧ u = x * y , •)"));
  }

  @Test
  public void testKnownCalculation() throws CustomParserException {
    PartialProof pp = setupProof();
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.parse("2.1");
    DeductionCalc step = DeductionCalc.createStep(pp, o, List.of(pos)).get();
    assertTrue(step.commandDescription(null).equals("calc L2.1"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals("We use CALC at position L2.1.\n\n"));
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (• , iter(1 + (2 + 3), u + z, x + y) ≈ x + y | x ≥ 0 ∧ u = x * y , •)"));
  }

  @Test
  public void testMultipleKnownCalculations() throws CustomParserException {
    PartialProof pp = setupProof();
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Optional<OutputModule> o = Optional.of(module);
    // skip to E1
    pp.addProofStep(pp.getProofState().deleteTopEquation(), DeductionDelete.createStep(pp,o).get());
    DeductionCalc step = DeductionCalc.createStep(pp,o,List.of(
      EquationPosition.parse("L1"),
      EquationPosition.parse("L3"),
      EquationPosition.parse("R1"))).get();
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (• , iter(a, x * 2, u) ≈ iter(z, u + 12, 17) | a = x + y ∧ x / y = u ∧ -y = z , •)"));
    step.explain(module);
    assertTrue(module.toString().equals("We use CALC at positions L1, L3 and R1.\n\n"));
  }

  @Test
  public void testUnknownCalculation() throws CustomParserException {
    PartialProof pp = setupProof();
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.parse("L3");
    DeductionCalc step = DeductionCalc.createStep(pp, o, List.of(pos)).get();
    assertTrue(step.commandDescription(null).equals("calc L3"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals("We use ALTER to add i1 = x + y to the constraint, " +
      "and then use CALC at position L3.\n\n"));
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (• , iter(1 + (2 + 3), x * y + z, i1) ≈ x + y | x ≥ 0 ∧ u = x * y ∧ i1 = x + y , •)"));
  }

  @Test
  public void testMultipleUnknownCalculation() throws CustomParserException {
    PartialProof pp = setupProof();
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos1 = EquationPosition.parse("L3");
    EquationPosition pos2 = EquationPosition.parse("R");
    DeductionCalc step = DeductionCalc.createStep(pp, o, List.of(pos1, pos2)).get();
    assertTrue(step.commandDescription(null).equals("calc L3 R"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals("We use ALTER to add i1 = x + y to the constraint, " +
      "and then use CALC at positions L3 and R.\n\n"));
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (• , iter(1 + (2 + 3), x * y + z, i1) ≈ i1 | x ≥ 0 ∧ u = x * y ∧ i1 = x + y , •)"));
  }

  @Test
  public void testBiggerKnownCalculation() throws CustomParserException {
    PartialProof pp = setupProof();
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.parse("L1");
    DeductionCalc step = DeductionCalc.createStep(pp, o, List.of(pos)).get();
    assertTrue(step.commandDescription(null).equals("calc L1"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals("We use CALC at position L1.\n\n"));
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (• , iter(6, x * y + z, x + y) ≈ x + y | x ≥ 0 ∧ u = x * y , •)"));
  }

  @Test
  public void testBiggerUnknownCalculation() throws CustomParserException {
    PartialProof pp = setupProof();
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.parse("L2");
    DeductionCalc step = DeductionCalc.createStep(pp, o, List.of(pos)).get();
    step.explain(module);
    assertTrue(module.toString().equals("We use ALTER to add i1 = x * y + z to the constraint, " +
      "and then use CALC at position L2.\n\n"));
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (• , iter(1 + (2 + 3), i1, x + y) ≈ x + y | x ≥ 0 ∧ u = x * y ∧ i1 = x * y + z , •)"));
  }

  @Test
  public void testMultiStepRightOrder() throws CustomParserException {
    PartialProof pp = setupProof();
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.parse("L2");
    DeductionCalc step = DeductionCalc.createStep(pp, o, List.of(
      EquationPosition.parse("L1.2"), EquationPosition.parse("L2.1"),
      EquationPosition.parse("L2"), EquationPosition.parse("L1"))).get();
    step.explain(module);
    assertTrue(module.toString().equals("We use ALTER to add i1 = u + z to the constraint, and " +
      "then use CALC at positions L1.2, L2.1, L2 and L1.\n\n"));
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (• , iter(6, i1, x + y) ≈ x + y | x ≥ 0 ∧ u = x * y ∧ i1 = u + z , •)"));
  }

  @Test
  public void testMultistepWrongOrder() throws CustomParserException {
    PartialProof pp = setupProof();
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Optional<OutputModule> o = Optional.of(module);
    EquationPosition pos = EquationPosition.parse("L2");
    assertTrue(DeductionCalc.createStep(pp, o, List.of(EquationPosition.parse("L1"),
      EquationPosition.parse("L1.2"))).isEmpty());
    assertTrue(module.toString().equals(
      "Subterm at position L1.2 has already been calculated away!\n\n"));
  }
}

