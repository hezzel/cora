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
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.Optional;

import charlie.util.Pair;
import charlie.util.FixedList;
import charlie.types.Type;
import charlie.terms.replaceable.*;
import charlie.terms.*;
import charlie.substitution.MutableSubstitution;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.Valuation;
import charlie.smt.SmtProblem;
import charlie.smt.SmtSolver;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class DeductionDisproveTheoryTest {
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

  public PartialProof setupProof(String left, String right, String constr) {
    TRS trs = setupTRS();
    MutableRenaming renaming = new MutableRenaming(trs.queryFunctionSymbolNames());
    Variable a = TermFactory.createVar("A", CoraInputReader.readType("Int -> Int -> Int"));
    renaming.setName(a, "A");
    Term le = CoraInputReader.readTermAndUpdateNaming(left, renaming, trs);
    Term ri = CoraInputReader.readTermAndUpdateNaming(right, renaming, trs);
    Term co = CoraInputReader.readTermAndUpdateNaming(constr, renaming, trs);
    TermPrinter printer = new TermPrinter(Set.of());
    return new PartialProof(trs,
      FixedList.of(new EquationContext(new Equation(le, ri, co), 11, renaming)),
      lst -> printer.generateUniqueNaming(lst));
  }

  @Test
  public void testHigherOrderNotOkay() {
    PartialProof pp = setupProof("A", "[+]", "true");
    MutableSubstitution subst = new MutableSubstitution();
    TRS trs = pp.getContext().getTRS();
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    subst.extend(renaming.getReplaceable("A"), TheoryFactory.timesSymbol);
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    assertTrue(DeductionDisproveTheory.createStep(pp, o, subst) == null);
    assertTrue(module.toString().equals("The left- and right-hand sides of the " +
      "equation do not have base type.\n\n"));
  }

  @Test
  public void testIncompleteState() {
    PartialProof pp = setupProof("1", "0", "true");
    MutableSubstitution subst = new MutableSubstitution();
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    // change the top equation to an incomplete one
    ProofState newstate =
      pp.getProofState().setIncomplete(pp.getProofState().getTopEquation().getIndex());
    pp.addProofStep(newstate, DeductionInduct.createStep(pp, o));
    assertTrue(DeductionDisproveTheory.createStep(pp, o, subst) == null);
    assertTrue(module.toString().equals(
      "DISPROVE can only be applied on complete equation contexts.\n\n"));
  }

  @Test
  public void testSuccess() {
    PartialProof pp = setupProof("4", "A(y, 1)", "y > 2 ∧ y < 5");
    MutableSubstitution subst = new MutableSubstitution();
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    subst.extend(renaming.getReplaceable("A"), TheoryFactory.plusSymbol);
    subst.extend(renaming.getReplaceable("y"), TheoryFactory.createValue(4));
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionDisproveTheory step = DeductionDisproveTheory.createStep(pp, o, subst);
    assertTrue(step.commandDescription().equals("disprove theory with [A := [+], y := 4]"));
    Settings.smtSolver = null;
    step.explain(module);
    assertTrue(step.verifyAndExecute(pp, o));
    step.explain(module);
    String txt = "We apply DISPROVE to E11, which succeeds because under the substitution " +
      "[A := [+], y := 4], the constraint y > 2 ∧ y < 5 evaluates to true, while the sides " +
      "of the equation can be calculated to 4 and 5 respectively.\n\n";
    assertTrue(module.toString().equals(txt + txt));
  }

  @Test
  public void testFailDueToEquality() {
    PartialProof pp = setupProof("4", "y + 1", "y > 2 ∧ y < 4");
    OutputModule module = OutputModule.createUnitTestModule();
    MutableSubstitution subst = new MutableSubstitution();
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    subst.extend(renaming.getReplaceable("y"), TheoryFactory.createValue(3));
    Optional<OutputModule> o = Optional.of(module);
    DeductionDisproveTheory step = DeductionDisproveTheory.createStep(pp, o, subst);
    Settings.smtSolver = null;
    assertFalse(step.verifyAndExecute(pp, o));
    assertFalse(pp.getProofState().isFinalState());
    assertTrue(step.commandDescription().equals("disprove theory with [y := 3]"));
    assertTrue(module.toString().equals("DISPROVE cannot be applied with the given " +
      "substitution, since the instantiated left- and right-hand side both evaluate to 4.\n\n"));
  }

  @Test
  public void testFailDueToConstraint() {
    PartialProof pp = setupProof("4", "y + 1", "y > 2 ∧ y < 4");
    OutputModule module = OutputModule.createUnitTestModule();
    MutableSubstitution subst = new MutableSubstitution();
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    subst.extend(renaming.getReplaceable("y"), TheoryFactory.createValue(4));
    Optional<OutputModule> o = Optional.of(module);
    DeductionDisproveTheory step = DeductionDisproveTheory.createStep(pp, o, subst);
    Settings.smtSolver = null;
    assertFalse(step.verifyAndExecute(pp, o));
    assertFalse(pp.getProofState().isFinalState());
    assertTrue(step.commandDescription().equals("disprove theory with [y := 4]"));
    assertTrue(module.toString().equals("DISPROVE cannot be applied with the given " +
      "substitution [y := 4], since the instantiated constraint evaluates to false.\n\n"));
  }
}

