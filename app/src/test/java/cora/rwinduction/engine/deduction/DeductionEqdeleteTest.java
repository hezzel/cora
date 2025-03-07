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
import charlie.terms.Term;
import charlie.terms.TermPrinter;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.SmtProblem;
import charlie.smt.SmtSolver;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class DeductionEqdeleteTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "f :: Int -> Unit -> Unit\n" +
      "g :: Int -> Unit\n" +
      "h :: List -> List\n" +
      "i :: (Int -> Bool) -> Int\n" +
      "j :: Int -> Int\n" +
      "k :: (| Int, Int |) -> Int -> Int\n" +
      "l :: Int -> Int -> (| Int, Int |)\n" +
      "q :: (Int -> Unit) -> Int -> Unit\n" +
      "a :: Int\n");
  }

  public PartialProof setupProof(String eqdesc) {
    TRS trs = setupTRS();
    TermPrinter printer = new TermPrinter(Set.of());
    return new PartialProof(trs,
      EquationParser.parseEquationList("j(x) = j(y) | x ≥ y ; " + eqdesc, trs),
      lst -> printer.generateUniqueNaming(lst));
  }

  class MySmtSolver implements SmtSolver {
    boolean _valid;
    String _storage;
    MySmtSolver(boolean answer) { _valid = answer; _storage = null; }
    public Answer checkSatisfiability(SmtProblem problem) { return new Answer.NO(); }
    public boolean checkValidity(SmtProblem problem) {
      _storage = problem.toString();
      return _valid;
    }
  }

  private OutputModule _module;
  private MySmtSolver _solver;

  private void testSuccess(String eqdesc) {
    PartialProof pp = setupProof(eqdesc);
    _module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(_module);
    Optional<DeductionEqdelete> step = DeductionEqdelete.createStep(pp, o);
    if (step.isEmpty()) {
      System.out.println(_module.toString());
      assertTrue(false, "Step is unsuccessful when it shouldn't be.");
    }
    _solver = new MySmtSolver(true);
    Settings.smtSolver = _solver;
    assertTrue(step.get().verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getTopEquation().getIndex() == 1);
    assertTrue(pp.getProofState().getHypotheses().size() == 0);
    assertTrue(pp.getCommandHistory().size() == 1);
    assertTrue(pp.getCommandHistory().get(0).equals("eq-delete"));
    assertTrue(_module.toString().equals(""));
    step.get().explain(_module);
  }

  @Test
  public void testSuccessfulDeleteOneArgument() {
    testSuccess("g(x) = g(y) | x = y");
    assertTrue(_solver._storage.equals("(i1 # i2) or (i1 = i2)\n"));
    assertTrue(_module.toString().equals("We observe that x = y ⊨ x = y, and may therefore " +
      "apply EQ-DELETION to remove E2 from the proof state.\n\n"));
  }

  @Test
  public void testSuccessfulDeleteTwoArguments() {
    testSuccess("f(3, g(x)) = f(x, g(17)) | true");
    assertTrue(_solver._storage.equals("false or ((3 = i1) and (i1 = 17))\n"));
    assertTrue(_module.toString().equals("We observe that true ⊨ 3 = x ∧ x = 17, and may " +
      "therefore apply EQ-DELETION to remove E2 from the proof state.\n\n"));
  }

  private void testFailToCreate(String eqdesc) {
    PartialProof pp = setupProof(eqdesc);
    _module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(_module);
    Optional<DeductionEqdelete> step = DeductionEqdelete.createStep(pp, o);
    assertTrue(step.isEmpty());
  }

  @Test
  public void testFailedCreateDifferentPositionCounts() {
    testFailToCreate("f(x, y) = f(3, g(z)) | true");
    assertTrue(_module.toString().equals("There is no suitable context for both sides: they " +
      "have a different number of subterms (note that you can only use EQ-DELETE if the terms " +
      "to be equated are variables or values -- not more sophisticated theory terms).\n\n"));
  }

  @Test
  public void testFailedCreateDifferentPositions() {
    testFailToCreate("f(j(x), y) = f(3, g(z)) | true");
    assertTrue(_module.toString().equals("There is no suitable context for both sides: their " +
      "position lists are not the same.\n\n"));
  }

  @Test
  public void testFailedCreateDifferentStructure() {
    testFailToCreate("k(l(x, 12), z) = k((| y, x |), y) | x = z");
    assertTrue(_module.toString().equals("There is no suitable context for both sides: " +
      "subterms l(x, 12) and ⦇y, x⦈ cannot be equated.\n\n"));
  }

  @Test
  public void testFailedCreateIllegalStructure() {
    testFailToCreate("q(λx.g(x), y) = q(λx.g(x), z)");
    assertTrue(_module.toString().equals("Subterm λx.g(x) is a kind of term that is not " +
      "currently supported in the rewriting induction module (at least not in " +
      "EQ-DELETION).\n\n"));
  }

  @Test
  public void testFailedCreateActuallyJustDeletion() {
    testFailToCreate("f(j(x), y) = f(j(x), y) | x = x");
    assertTrue(_module.toString().equals("No subterms to be equated; use DELETION instead!\n\n"));
  }

  @Test
  public void testFailedCreateConstantOnTheRight() {
    testFailToCreate("g(x) = g(a)");
    assertTrue(_module.toString().equals("Failed to equate x and a: they cannot be moved into " +
      "the constraint because a is not a theory term.\n\n"));
  }

  @Test
  public void testFailedCreateConstantOnTheLeft() {
    testFailToCreate("g(a) = g(x)");
    assertTrue(_module.toString().equals("Failed to equate a and x: they cannot be moved into " +
      "the constraint because a is not a theory term.\n\n"));
  }

  @Test
  public void testFailedCreateDifferentValues() {
    testFailToCreate("f(3, x) = f(4, x)");
    assertTrue(_module.toString().equals("Failed to equate distinct values (3 and 4).\n\n"));
  }

  @Test
  public void testFailedCreateNonTheoryTypes() {
    testFailToCreate("h(x) = h(y)");
    assertTrue(_module.toString().equals("Failed to equate x and y: they cannot be moved into " +
      "the constraint because the type List is not a theory sort.\n\n"));
  }

  @Test
  public void testFailedCreateHigherTypes() {
    testFailToCreate("i(F) = i(G)");
    assertTrue(_module.toString().equals("Failed to equate F and G: they cannot be moved into " +
      "the constraint because the type Int → Bool is not a theory sort.\n\n"));
  }

  @Test
  public void testFailedVerification() {
    PartialProof pp = setupProof("f(x) = f(3) | x > 2");
    _module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(_module);
    DeductionEqdelete step = DeductionEqdelete.createStep(pp, o).get();
    _solver = new MySmtSolver(false);
    Settings.smtSolver = _solver;
    assertFalse(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getEquations().size() == 2);
    assertTrue(_module.toString().equals("The EQ-DELETION rule is not obviously applicable: " +
      "I could not prove that x > 2 ⊨ x = 3.\n\n"));
  }
}

