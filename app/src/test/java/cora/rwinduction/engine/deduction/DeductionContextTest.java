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
import java.util.Optional;

import charlie.util.FixedList;
import charlie.util.Pair;
import charlie.terms.position.PositionFormatException;
import charlie.terms.position.Position;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.TermPrinter;
import charlie.terms.TermFactory;
import charlie.substitution.MutableSubstitution;
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
    assertTrue(pp.getProofState().getIncompleteEquations().isEmpty());
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
      "(Use \"context\" for the more general form, which does, however, lose completeness in " +
      "this case.)\n\n"));
    module = OutputModule.createUnitTestModule();
    o = Optional.of(module);
    DeductionContext step = DeductionContext.createStep(pp, o, false);
    assertTrue(step.verifyAndExecute(pp, o));
    step.explain(module);
    assertTrue(module.toString().equals("We apply CONTEXT to E2, splitting the immediate " +
      "arguments into separate equations.  We lose the completeness flag.\n\n"));
  }

  @Test
  public void testCreateStepWithVariables() {
    PartialProof pp = setupProof("@(F, sum1(x)) = @(F, sum2(x))");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Settings.setStrategy(Settings.Strategy.Full);
    DeductionSimplify simpl = DeductionSimplify.createStep(pp, o, "R8",
      EquationPosition.TOPLEFT, new MutableSubstitution());
    assertTrue(simpl.verifyAndExecute(pp, o));
    simpl = DeductionSimplify.createStep(pp, o, "R8",
      EquationPosition.TOPRIGHT, new MutableSubstitution());
    assertTrue(simpl.verifyAndExecute(pp, o));
    assertTrue(DeductionContext.createStep(pp, o, true) == null);
    assertTrue(module.toString().equals("The semiconstructor rule can only be applied if both " +
      "sides of the equation have a form f s1 ... sn, with f a function symbol and n < ar(f).  " +
      "(Use \"context\" for the more general form, which does, however, lose completeness in " +
      "this case.)\n\n"));
    DeductionContext step = DeductionContext.createStep(pp, o, false);
    assertTrue(step.verify(o));
    assertTrue(step.commandDescription().equals("context"));
    assertFalse(step.isComplete());
    assertTrue(pp.getProofState().getIncompleteEquations().isEmpty());
    assertTrue(step.execute(pp, o));
    assertTrue(pp.getProofState().getIncompleteEquations().contains(5));
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
      "have the same head.\n\nThe context rule cannot be applied, because the two sides of " +
      "the equation do not have the same head.\n\n"));
  }

  @Test
  public void testCreateCompleteStepWithPositions() throws PositionFormatException {
    PartialProof pp = setupProof("append(cons(sum1(x), y)) = append(cons(sum2(z), nil)) | x = z");
    List<Position> positions = List.of(Position.parse("1.1"), Position.parse("1.2"));
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionContext step = DeductionContext.createStep(pp, o, positions);
    assertTrue(step.isComplete());
    assertTrue(step.commandDescription().equals("context 1.1 1.2"));
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getIncompleteEquations().isEmpty());
    assertTrue(pp.getProofState().getEquations().size() == 3);
    assertTrue(pp.getProofState().getEquations().get(1).toString().equals(
      "E3: (• , y ≈ nil | x = z , •)"));
    assertTrue(pp.getProofState().getEquations().get(2).toString().equals(
      "E4: (• , sum1(x) ≈ sum2(z) | x = z , •)"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply CONTEXT to E2, splitting the immediate " +
      "arguments into separate equations.  We preserve the completeness flag.\n\n"));
  }

  @Test
  public void testCreateIncompleteStepWithPositions() throws PositionFormatException {
    PartialProof pp = setupProof(
      "{ F :: Int -> list -> list } append(F(sum1(x), y)) = append(F(sum2(z), nil)) | x = z");
    List<Position> positions = List.of(Position.parse("1.1"), Position.parse("1.2"));
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionContext step = DeductionContext.createStep(pp, o, positions);
    assertFalse(step.isComplete());
    assertTrue(step.commandDescription().equals("context 1.1 1.2"));
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getIncompleteEquations().size() == 2);
    assertTrue(pp.getProofState().getEquations().size() == 3);
    step.explain(module);
    assertTrue(module.toString().equals("We apply CONTEXT to E2, splitting the immediate " +
      "arguments into separate equations.  We lose the completeness flag.\n\n"));
  }

  @Test
  public void testCompletenessIrrelevant() throws PositionFormatException {
    PartialProof pp = setupProof("{ F :: list -> list } F(cons(x, cons(y, nil))) = " +
      "F(cons(a, cons(b, nil))) | x + y = a + b");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionContext step = DeductionContext.createStep(pp, o, false);
    assertTrue(step.verifyAndExecute(pp, o));
    List<Position> positions = List.of(Position.parse("1"), Position.parse("2.1"));
    step = DeductionContext.createStep(pp, o, positions);
    assertTrue(step.isComplete());
    step.explain(module);
    assertTrue(module.toString().equals("We apply CONTEXT to E3, splitting the immediate " +
      "arguments into separate equations.\n\n"));
  }

  @Test
  public void testCreateStepWhereSomePositionDoesNotExist() throws PositionFormatException {
    PartialProof pp = setupProof(
      "{ F :: Int -> list -> list } append(F(sum1(x), y)) = append(F(sum2(z), y)) | x = z");
    List<Position> positions = List.of(Position.parse("1.1"), Position.parse("1.2.1"));
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    assertTrue(DeductionContext.createStep(pp, o, positions) == null);
    assertTrue(module.toString().equals("There is no position 1.2.1: the subterm at position " +
      "1.2 has no arguments!\n\n"));
  }

  @Test
  public void testCreateStepWithPartialPosition() throws PositionFormatException {
    PartialProof pp = setupProof("append(cons(sum1(x), y)) = append(cons(sum2(z), y)) | x = z");
    List<Position> positions = List.of(Position.parse("1.*1"));
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    assertTrue(DeductionContext.createStep(pp, o, positions) == null);
    assertTrue(module.toString().equals("The context rule cannot be applied with a partial " +
      "position 1.☆1.\n\n"));
  }

  @Test
  public void testCreateStepWithNonParallelPositions() throws PositionFormatException {
    PartialProof pp = setupProof("append(cons(sum1(x), y)) = append(cons(sum2(z), y)) | x = z");
    List<Position> positions = List.of(Position.parse("1.1"), Position.parse("1"));
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    assertTrue(DeductionContext.createStep(pp, o, positions) == null);
    assertTrue(module.toString().equals("The given positions are not parallel.\n\n"));
  }

  @Test
  public void testCreateStepWithIncorrectlyOrderedPositions() throws PositionFormatException {
    PartialProof pp = setupProof("append(cons(sum1(x), y)) = append(cons(sum2(z), nil)) | x = z");
    List<Position> positions = List.of(Position.parse("1.2"), Position.parse("1.1"));
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionStep step = DeductionContext.createStep(pp, o, positions);
    assertTrue(step.commandDescription().equals("context 1.2 1.1"));
    assertTrue(step.verifyAndExecute(pp, o));
    // the one at the first given position is the top equation
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E4: (• , y ≈ nil | x = z , •)"));
  }

  @Test
  public void testCreateStepWithDifferentContextAboveBox() throws PositionFormatException {
    PartialProof pp = setupProof(
      "{ F :: Int -> list -> list } append(F(sum1(x), y)) = append(cons(sum2(z), y)) | x = z");
    List<Position> positions = List.of(Position.parse("1.2"), Position.parse("1.1"));
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    assertTrue(DeductionContext.createStep(pp, o, positions) == null);
    assertTrue(module.toString().equals("The context rule is not applicable, since the subterms " +
      "at position 1 have different head terms (F and cons).\n\n"));
  }

  @Test
  public void testCreateStepWithDifferentContextParallelToBox() throws PositionFormatException {
    PartialProof pp = setupProof("append(cons(sum1(x), y)) = append(cons(sum2(z), nil)) | x = z");
    List<Position> positions = List.of(Position.parse("1.1"));
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    assertTrue(DeductionContext.createStep(pp, o, positions) == null);
    assertTrue(module.toString().equals("The subterms at position 1.2 are not the same.\n\n"));
  }

  @Test
  public void testCreateStepWithLambdaPosition() throws PositionFormatException {
    PartialProof pp = setupProof("append(cons(sum1(x), y)) = append(cons(sum2(z), nil)) | x = z");
    List<Position> positions = List.of(Position.parse("1.0"), Position.parse("1.1"));
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    assertTrue(DeductionContext.createStep(pp, o, positions) == null);
    assertTrue(module.toString().equals("Unexpected position: 1.0.  This does not represent a " +
      "position in a fully applicative term.\n\n"));
  }

  @Test
  public void testDifferences() {
    TRS trs = CoraInputReader.readTrsFromString(
      "end :: Int -> Tree\n" +
      "cons :: Tree -> Tree -> Tree\n" +
      "merge :: Tree -> Tree -> Tree\n" +
      "merge(x, y) -> cons(x, y)\n"
    );
    MutableRenaming renaming = new MutableRenaming(trs.queryFunctionSymbolNames());
    Variable f = TermFactory.createVar("F", CoraInputReader.readType("Tree -> Tree -> Tree"));
    renaming.setName(f, "F");
    Term s = CoraInputReader.readTermAndUpdateNaming("cons(cons(cons(end(1), end(2)), " +
      "cons(end(3), merge(end(4), end(5)))), cons(end(6), y))", renaming, trs);
    Term t = CoraInputReader.readTermAndUpdateNaming("cons(cons(cons(end(1), end(i)), " +
      "F(end(3), cons(end(4), end(5)))), cons(y, end(7)))", renaming, trs);
    ArrayList<Position> posses = new ArrayList<Position>();
    ArrayList<Pair<Term,Term>> pairs = new ArrayList<Pair<Term,Term>>();
    DeductionContext.storeDifferences(s, t, new ProofContext(trs, lst -> renaming), posses, pairs);
    assertTrue(posses.size() == 4);
    assertTrue(pairs.size() == 4);

    assertTrue(posses.get(0).toString().equals("1.1.2.1"));
    assertTrue(pairs.get(0).fst().toString().equals("2"));
    assertTrue(pairs.get(0).snd().toString().equals("i"));

    assertTrue(posses.get(1).toString().equals("1.2"));
    assertTrue(pairs.get(1).fst().toString().equals("cons(end(3), merge(end(4), end(5)))"));
    assertTrue(pairs.get(1).snd().toString().equals("F(end(3), cons(end(4), end(5)))"));

    assertTrue(posses.get(2).toString().equals("2.1"));
    assertTrue(pairs.get(2).fst().toString().equals("end(6)"));
    assertTrue(pairs.get(2).snd().toString().equals("y"));

    assertTrue(posses.get(3).toString().equals("2.2"));
    assertTrue(pairs.get(3).fst().toString().equals("y"));
    assertTrue(pairs.get(3).snd().toString().equals("end(7)"));
  }

}

