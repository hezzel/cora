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

import charlie.util.FixedList;
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

class DeductionGeneraliseSubtermTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "iter :: Int -> Int -> Int -> Int\n" +
      "iter(x, i, z) -> z | i > x\n" +
      "iter(x, i, z) -> iter(x, i+1, z+i) | i <= x\n");
  }

  public PartialProof setupProof(String condesc) {
    TRS trs = setupTRS();
    TermPrinter printer = new TermPrinter(Set.of());
    EquationContext context = EquationParser.parseEquationContext(condesc, 1, trs);
    return new PartialProof(trs, FixedList.of(context), lst -> printer.generateUniqueNaming(lst));
  }

  @Test
  public void testGeneraliseBothWithNoBoundingTerms() {
    PartialProof pp =
      setupProof("(•,{ F :: Int -> Int } iter(F(x), F(y), F(x)) = iter(y, x, F(x)) | x > y,•)");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term subterm = CoraInputReader.readTerm("F(x)", renaming, pp.getContext().getTRS());
    DeductionGeneraliseSubterm dgs = DeductionGeneraliseSubterm.createStep(pp, o, subterm, "v");
    assertTrue(dgs.commandDescription().equals("generalise subterm F(x) as v"));
    dgs.explain(module);
    assertTrue(module.toString().equals(
      "We apply GENERALISE to replace the equation context E1 by " +
      "E2: (• , iter(v, F(y), v) ≈ iter(y, x, v) | x > y , •).\n\n"));
    assertTrue(dgs.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , iter(v, F(y), v) ≈ iter(y, x, v) | x > y , •)"));
  }

  private void testSuccess(String eqcon, String subterm, String varname, String result) {
    PartialProof pp = setupProof(eqcon);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term sub = CoraInputReader.readTerm(subterm, renaming, pp.getContext().getTRS());
    Optional<OutputModule> o = Optional.of(OutputModule.createUnitTestModule());
    DeductionGeneraliseSubterm dgs = DeductionGeneraliseSubterm.createStep(pp, o, sub, varname);
    assertTrue(dgs.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals("E2: " + result));
  }

  @Test
  public void testGeneraliseLeftWithBoundingTerms() {
    testSuccess("(1000, { F :: Int -> Int } iter(F(x), F(y), F(x)) = iter(y, x, F(z)) | " +
                  "x > y, iter(x, y, y))",
                "F(x)", "v",
                "(iter(v, F(y), v) , iter(v, F(y), v) ≈ iter(y, x, F(z)) | x > y , iter(x, y, y))");
  }

  @Test
  public void testGeneraliseRightWithBoundingTerms() {
    testSuccess("(1000, { F :: Int -> Int } iter(F(z), F(y), F(z)) = iter(y, x, F(x)) | " +
                  "x > y, iter(x, y, y))",
                "F(x)", "v",
                "(1000 , iter(F(z), F(y), F(z)) ≈ iter(y, x, v) | x > y , iter(y, x, v))");
  }

  @Test
  public void testSubtermOfBoundingTerm() {
    testSuccess("(1000, { F :: Int -> Int } iter(F(x), F(y), F(x)) = iter(y, x, F(z)) | " +
                  "x > y, iter(x, F(x), y))",
                "F(x)", "v",
                "(iter(v, F(y), v) , iter(v, F(y), v) ≈ iter(y, x, F(z)) | " +
                  "x > y , iter(y, x, F(z)))");
  }

  @Test
  public void testSubtermInRightAndConstraint() {
    testSuccess("(900 , iter(x, y, z) ≈ iter(y, x + 1, z) | x + 1 > y , 1000)",
                "x + 1", "a",
                "(iter(x, y, z) , iter(x, y, z) ≈ iter(y, a, z) | a > y , iter(y, a, z))");
  }

  private void testFailure(String eqcon, String subterm, String varname, String result) {
    PartialProof pp = setupProof(eqcon);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term sub = CoraInputReader.readTerm(subterm, renaming, pp.getContext().getTRS());
    OutputModule o = OutputModule.createUnitTestModule();
    assertTrue(DeductionGeneraliseSubterm.createStep(pp, Optional.of(o), sub, varname) == null);
    assertTrue(o.toString().equals(result + "\n\n"), o.toString());
  }

  @Test
  public void testVariableNameNotFresh() {
    testFailure("(a + 1, iter(x, y, z + 1) ≈ iter(x, y, z) | x > 0, b - 0)", "z + 1", "a",
                "The variable name a is not fresh.");
  }

  @Test
  public void testVariableNameIsAFunction() {
    testFailure("(a + 1, iter(x, y, z + 1) ≈ iter(x, y, z) | x > 0, b - 0)", "z + 1", "iter",
                "The name iter is not a legal variable name.");
  }

  @Test
  public void testNoSuchSubterm() {
    testFailure("(iter(x + 1, y, z), iter(x, y, z) = iter(z, y, x) | x > 0, iter(z, y, x))",
                "x + 1", "v", "No such subterm in the equation: x + 1");
  }
}

