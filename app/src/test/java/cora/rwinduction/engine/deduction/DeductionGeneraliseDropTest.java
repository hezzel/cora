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
import java.util.ArrayList;
import java.util.Optional;
import java.util.Set;

import charlie.util.Pair;
import charlie.types.TypeFactory;
import charlie.terms.replaceable.Renaming;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.Valuation;
import charlie.smt.SmtProblem;
import charlie.smt.SmtSolver;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class DeductionGeneraliseDropTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "iter :: Int -> Int -> Int -> Int\n" +
      "iter(x, i, z) -> z | i > x\n" +
      "iter(x, i, z) -> iter(x, i+1, z+i) | i <= x\n");
  }

  public PartialProof setupProof(String eqdesc) {
    TRS trs = setupTRS();
    TermPrinter printer = new TermPrinter(Set.of());
    return new PartialProof(trs, EquationParser.parseEquationList(eqdesc, trs),
      lst -> printer.generateUniqueNaming(lst));
  }

  @Test
  public void testDropOneSuccess() {
    PartialProof pp = setupProof("iter(x, i, z) = iter(i, z, x) | x > i ∧ z != 0 ∧ x <= z");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term drop = CoraInputReader.readTerm("z != 0", renaming, pp.getContext().getTRS());
    DeductionGeneraliseDrop dgd = DeductionGeneraliseDrop.createStep(pp, o, drop);
    assertTrue(dgd.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getTopEquation().getIndex() == 2);
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , iter(x, i, z) ≈ iter(i, z, x) | x > i ∧ x ≤ z , •)"));
    dgd.explain(module);
    assertTrue(module.toString().equals(
      "We apply GENERALISE to replace the constraint of E1 by x > i ∧ x ≤ z.\n\n"));
  }

  @Test
  public void testDropMultiple() {
    PartialProof pp = setupProof("iter(x, y, z) = iter(z, y, x) | x > 1 ∧ y > 1 ∧ z > 1 ∧ x != z");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term drop = CoraInputReader.readTerm("x != z ∧ x > 1", renaming, pp.getContext().getTRS());
    DeductionGeneraliseDrop dgd = DeductionGeneraliseDrop.createStep(pp, o, drop);
    dgd.execute(pp, o);
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , iter(x, y, z) ≈ iter(z, y, x) | y > 1 ∧ z > 1 , •)"));
  }

  @Test
  public void testDropFirst() {
    PartialProof pp = setupProof("iter(x, y, z) = iter(z, y, x) | x > 1 ∧ y < 1 ∧ z > 1 ∧ y < 1");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term drop = CoraInputReader.readTerm("y < 1 ∧ z > 1", renaming, pp.getContext().getTRS());
    DeductionGeneraliseDrop dgd = DeductionGeneraliseDrop.createStep(pp, o, drop);
    dgd.execute(pp, o);
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , iter(x, y, z) ≈ iter(z, y, x) | x > 1 ∧ y < 1 , •)"));
  }

  @Test
  public void testDropFailure() {
    PartialProof pp = setupProof("iter(x, y, z) = iter(z, y, x) | z > 0 ∧ x > 1 ∧ y = 0");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term drop = CoraInputReader.readTerm("y = 0 ∧ x ≥ 1 ∧ z < 0", renaming, pp.getContext().getTRS());
    assertTrue(DeductionGeneraliseDrop.createStep(pp, o, drop) == null);
    assertTrue(module.toString().equals("No such subterm in the constraint: x ≥ 1.\n\n"));
  }
}

