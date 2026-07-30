/**************************************************************************************************
 Copyright 2026 Cynthia Kop

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
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.FixedAnswerValidityChecker;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class DeductionAlterObserveTest {
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
      "extra :: list -> list -> Int\n");
  }

  public PartialProof setupProof(String eqdesc) {
    TRS trs = setupTRS();
    return new PartialProof(trs, EquationParser.parseEquationList(eqdesc, trs),
      trs.createNameGenerator());
  }

  private PartialProof createPartialProof(String equation, Optional<OutputModule> o) {
    PartialProof pp = setupProof(equation);
    DeductionInduct induct = DeductionInduct.createStep(pp, o);
    induct.execute(pp, o);
    return pp;
  }

  private DeductionAlterObserve createStep(PartialProof pp, Optional<OutputModule> o,
                                           String orig, String repl) {
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Variable x = (Variable)pp.getProofState().getTopEquation().getRenaming().getReplaceable(orig);
    Term replacement = CoraInputReader.readTerm(repl, renaming, pp.getContext().getTRS());
    return DeductionAlterObserve.createStep(pp, o, x, replacement);
  }

  @Test
  public void testAlterToValue() {
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    PartialProof pp = createPartialProof("sum1(x) = iter(x, i, y) | i = 0", o);
    DeductionAlterObserve step = createStep(pp, o, "x", "3");
    
    assertTrue(step.commandDescription().equals("alter observe x = 3"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply ALTER to replace x in the left- and right-hand " +
      "side of the equation by 3.\n\n"));

    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (sum1(x) , sum1(3) ≈ iter(3, i, y) | i = 0 , iter(x, i, y))"));
  }

  @Test
  public void testAlterToVariable() {
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    PartialProof pp = createPartialProof("sum1(x) = sum2(y) | x = y ∧ y = 2 + 1", o);
    DeductionAlterObserve step = createStep(pp, o, "x", "y");
    
    assertTrue(step.commandDescription().equals("alter observe x = y"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply ALTER to replace x in the left- and right-hand " +
      "side of the equation by y.\n\n"));

    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E3: (sum1(x) , sum1(y) ≈ sum2(y) | x = y ∧ y = 2 + 1 , sum2(y))"));
  }

  @Test
  public void testOriginalDoesNotOccur() {
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    PartialProof pp = createPartialProof("sum1(x) = sum2(x) | x = y ∧ y = 2", o);
    assertTrue(createStep(pp, o, "y", "2") == null);
    assertTrue(module.toString().equals("Variable y does not occur in the left- or right-hand " +
      "side of the equation!\n\n"));
  }

  @Test
  public void testReplacementIsNotAValue() {
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    PartialProof pp = createPartialProof("sum1(x) = sum2(y) | x = y ∧ y = 2 + 1", o);
    assertTrue(createStep(pp, o, "y", "2 + 1") == null);
    assertTrue(module.toString().equals("Replacement in ALTER OBSERVE should be a variable or " +
      "value; 2 + 1 is neither!\n\n"));
  }

  @Test
  public void testDifferentTypes() {
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    PartialProof pp = createPartialProof("sum1(x) = sum2(y) | x = y", o);
    assertTrue(createStep(pp, o, "x", "true") == null);
    assertTrue(module.toString().equals("Both sides of the observed equality should have the " +
      "same type (given: Int versus Bool).\n\n"));
  }

  @Test
  public void testNonTheoryTypes() {
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    PartialProof pp = createPartialProof("extra(x, y) = sum1(0)", o);
    assertTrue(createStep(pp, o, "x", "y") == null);
    assertTrue(module.toString().equals("The input type should be a theory sort, but is " +
      "list.\n\n"));
  }

  @Test
  public void testEqualityCheckSucceeds() {
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    PartialProof pp = createPartialProof("sum1(x) = sum2(y) | x = y ∧ y = 2 + 1", o);
    DeductionAlterObserve step = createStep(pp, o, "x", "y");
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(true);
    Settings.smtSolver = solver;
    assertTrue(step.verify(o));
    assertTrue(module.toString().equals(""));
    assertTrue(solver.queryNumberQuestions() == 1);
    assertTrue(solver.queryQuestion(0).equals("(i1 # i2) or (i2 # 3) or (i1 = i2)"));
  }

  @Test
  public void testEqualityCheckFails() {
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    PartialProof pp = createPartialProof("sum1(x) = sum2(y) | x = y ∧ y = 2 + 1", o);
    DeductionAlterObserve step = createStep(pp, o, "y", "2");
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(false);
    Settings.smtSolver = solver;
    assertFalse(step.verify(o));
    assertTrue(module.toString().equals("It is not obvious if this usage of alteration is " +
      "permitted: I could not prove that x = y ∧ y = 2 + 1 ⇒ y = 2.\n\n"));
    assertTrue(solver.queryNumberQuestions() == 1);
    assertTrue(solver.queryQuestion(0).equals("(i1 # i2) or (i2 # 3) or (i2 = 2)"));
  }
}

