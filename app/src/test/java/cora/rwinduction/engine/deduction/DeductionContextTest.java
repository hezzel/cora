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

import charlie.util.FixedList;
import charlie.terms.Term;
import charlie.terms.TermPrinter;
import charlie.terms.TermFactory;
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

class DeductionContextTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "sum1 :: Int -> Int\n" +
      "sum1(x) -> 0 | x <= 0\n" +
      "sum1(x) -> x + sum1(x-1) | x > 0\n" +
      "sum2 :: Int -> Int\n" +
      "sum2(x) -> iter(x, 0, 0)\n" +
      "iter :: Int -> Int -> Int -> Int\n" +
      "iter(x, i, z) -> z | i > x\n" +
      "iter(x, i, z) -> iter(x, i+1, z+i) | i <= x\n" +
      "nil :: list\n" +
      "cons :: Int -> list -> list\n" +
      "append :: list -> list -> list\n" +
      "append(nil, x) -> x\n" +
      "append(cons(x, y), z) -> cons(x, append(y, z))\n" +
      "@ :: (Int -> Int) -> Int -> Int\n" +
      "@(F, x) -> F(x)\n");
  }

  public PartialProof setupProof(String eqdesc) {
    TRS trs = setupTRS();
    TermPrinter printer = new TermPrinter(Set.of());
    return new PartialProof(trs,
      EquationParser.parseEquationList("sum1(x) = sum2(x) | x ≥ 0 ; " + eqdesc, trs),
      lst -> printer.generateUniqueNaming(lst));
  }

  @Test
  public void testCreateSuccessfulStepWithConstructor() {
    PartialProof pp = setupProof("cons(sum1(x), nil) = cons(sum2(y), append(nil, nil)) | x = y");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionContext step = DeductionContext.createStep(pp, o, true);
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getEquations().size() == 3);
    assertTrue(pp.getProofState().getEquations().get(1).toString().equals(
      "E3: (• , nil ≈ append(nil, nil) | x = y , •)"));
    assertTrue(pp.getProofState().getEquations().get(2).toString().equals(
      "E4: (• , sum1(x) ≈ sum2(y) | x = y , •)"));
    assertTrue(pp.getProofState().getTopEquation().getIndex() == 4);
    assertTrue(pp.getProofState().getHypotheses().size() == 0);
    assertTrue(pp.getCommandHistory().size() == 1);
    assertTrue(pp.getCommandHistory().get(0).equals("semiconstructor"));
    assertTrue(module.toString().equals(""));
    step.explain(module);
    assertTrue(module.toString().equals(
      "We apply SEMICONSTRUCTOR to E2 since cons is a constructor symbol.\n\n"));
  }

  @Test
  public void testCreateSuccessfulStepWithPartialApplication() {
    PartialProof pp = setupProof("[+](sum1(x)) = [+](sum2(y + 1)) | x = y + 1");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionInduct induct = DeductionInduct.createStep(pp, o);
    induct.verifyAndExecute(pp, o);
    DeductionContext step = DeductionContext.createStep(pp, o, false);
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getEquations().size() == 2);
    assertTrue(pp.getProofState().getEquations().get(1).toString().equals(
      "E4: ([+](sum1(x)) , sum1(x) ≈ sum2(y + 1) | x = y + 1 , [+](sum2(y + 1)))"));
    assertTrue(pp.getCommandHistory().size() == 2);
    assertTrue(pp.getCommandHistory().get(1).equals("semiconstructor"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply SEMICONSTRUCTOR to E3, since the rule arity " +
      "of [+] is 2 and only 1 arguments are present.\n\n"));
  }

  @Test
  public void testCreateStepWithFullApplication() {
    PartialProof pp = setupProof("append(x, nil) = append(nil, x)");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    assertTrue(DeductionContext.createStep(pp, o, true) == null);
    assertTrue(module.toString().equals("The semiconstructor rule can only be applied if both " +
      "sides of the equation have a form f s1 ... sn, with f a function symbol and n < ar(f).  " +
      "(Use \"application\" for the more general form, which does, however, lose " +
      "completeness.)\n\n"));
    module = OutputModule.createUnitTestModule();
    o = Optional.of(module);
    DeductionContext step = DeductionContext.createStep(pp, o, false);
    assertTrue(step.verifyAndExecute(pp, o));
    step.explain(module);
    assertTrue(module.toString().equals("We apply APPLICATION to E2, splitting the immediate " +
      "arguments into separate equations.\n\n"));
  }

  @Test
  public void testCreateFailedStepWithVariables() {
    PartialProof pp = setupProof("@(F, sum1(x)) = @(F, sum2(x))");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Settings.setStrategy(Settings.Strategy.Full);
    DeductionSimplify simpl = DeductionSimplify.createStep(pp, o, "O8",
      EquationPosition.TOPLEFT, TermFactory.createEmptySubstitution());
    assertTrue(simpl.verifyAndExecute(pp, o));
    simpl = DeductionSimplify.createStep(pp, o, "O8",
      EquationPosition.TOPRIGHT, TermFactory.createEmptySubstitution());
    assertTrue(simpl.verifyAndExecute(pp, o));
    assertTrue(DeductionContext.createStep(pp, o, true) == null);
    assertTrue(module.toString().equals("The semiconstructor rule can only be applied if both " +
      "sides of the equation have a form f s1 ... sn, with f a function symbol and n < ar(f).  " +
      "(Use \"application\" for the more general form, which does, however, lose " +
      "completeness.)\n\n"));
    DeductionContext step = DeductionContext.createStep(pp, o, false);
    assertTrue(step.verify(o));
    assertTrue(step.commandDescription().equals("application"));
  }

  @Test
  public void testCreateFailedStepWithDifferentSymbols() {
    PartialProof pp = setupProof("cons(sum1(x)) = append(nil)");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    assertTrue(DeductionContext.createStep(pp, o, true) == null);
    assertTrue(DeductionContext.createStep(pp, o, false) == null);
    assertTrue(module.toString().equals(
      "The semiconstructor rule cannot be applied, because the two sides of the equation do not " +
      "have the same head.\n\nThe application rule cannot be applied, because the two sides of " +
      "the equation do not have the same head.\n\n"));
  }
}

