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

package cora.rwinduction.engine;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;
import java.util.Set;

import charlie.util.FixedList;
import charlie.terms.position.Position;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.Truth;
import charlie.smt.SmtProblem;
import charlie.smt.SmtSolver;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.rwinduction.parser.ExtendedTermParser;

class DeductionSimplifyTest {
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
      "input :: Int\n" +
      "input -> x | y > 0\n" +
      "tmp :: Int -> Int\n" +
      "tmp(x) -> 0\n");
  }

  public PartialProof setupProof(String eqdesc) {
    TRS trs = setupTRS();
    Equation eq = ExtendedTermParser.parseEquation(eqdesc, trs);
    return new PartialProof(trs, FixedList.of(eq), new TermPrinter(Set.of()));
  }

  private class MySmtSolver implements SmtSolver {
    private boolean _answer;
    String _question;
    public MySmtSolver(boolean answer) { _answer = answer; _question = null; }
    public Answer checkSatisfiability(SmtProblem problem) { assertTrue(false); return null; }
    public boolean checkValidity(SmtProblem prob) { _question = prob.toString(); return _answer; }
  }

  private class MySimpleSolver implements SmtSolver {
    public Answer checkSatisfiability(SmtProblem problem) { assertTrue(false); return null; }
    public boolean checkValidity(SmtProblem prob) {
      return prob.queryCombinedConstraint().simplify() instanceof Truth;
    }
  }

  @Test
  public void testSimplifyUnconstrained() {
    PartialProof pp = setupProof("sum1(x) = sum2(x) | x > 0");
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    MySmtSolver solver = new MySmtSolver(true);
    DeductionSimplify ds = new DeductionSimplify(pp, module);
    assertTrue(ds.apply("O3", EquationPosition.TOPRIGHT));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "sum1(x) ≈ iter(x, 0, 0) | x > 0"));
    assertTrue(pp.getCommandHistory().get(0).equals("simplify O3 R"));
    assertTrue(solver._question == null); // it doesn't get called for unconstrained rules
    assertTrue(module.toString().equals(""));
  }

  @Test
  public void testSimplifyConstrained() throws charlie.exceptions.CustomParserException {
    PartialProof pp = setupProof("sum1(z) + 0 = iter(z, 0, 0) | z > 0");
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    MySmtSolver solver = new MySmtSolver(true);
    Settings.smtSolver = solver;
    DeductionSimplify ds = new DeductionSimplify(pp, module);
    EquationPosition pos = new EquationPosition(EquationPosition.Side.Left, Position.parse("1"));
    assertTrue(ds.apply("O2", pos));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "z + sum1(z - 1) + 0 ≈ iter(z, 0, 0) | z > 0"));
    assertTrue(solver._question.equals("(0 >= i1) or (i1 >= 1)\n"));
    assertTrue(module.toString().equals(""));
  }

  @Test
  public void testSimplifyWithSubstitution() {
    PartialProof pp = setupProof("input = 7");
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Settings.smtSolver = new MySimpleSolver();
    DeductionSimplify ds = new DeductionSimplify(pp, module);
    Substitution subst = TermFactory.createEmptySubstitution();
    Variable x = pp.getRenaming("O6").getVariable("x");
    Variable y = pp.getRenaming("O6").getVariable("y");
    subst.extend(x, TheoryFactory.createValue(-1));
    subst.extend(y, TheoryFactory.createValue(8));
    assertTrue(ds.apply("O6", EquationPosition.TOPLEFT, subst));
    assertTrue(pp.getProofState().getTopEquation().toString().equals("-1 ≈ 7 | true"));
    assertTrue(pp.getCommandHistory().get(0).equals("simplify O6 L with [x := -1; y := 8]"));
    assertTrue(module.toString().equals(""));
  }

  @Test
  public void testSimplifyWithSubstitutionMappingToConstraintVar() {
    PartialProof pp = setupProof("input = 7 | z = 7");
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Settings.smtSolver = new MySimpleSolver();
    DeductionSimplify ds = new DeductionSimplify(pp, module);
    Substitution subst = TermFactory.createEmptySubstitution();
    Variable x = pp.getRenaming("O6").getVariable("x");
    Variable y = pp.getRenaming("O6").getVariable("y");
    Equation equation = pp.getProofState().getTopEquation();
    subst.extend(x, equation.getRenaming().getVariable("z"));
    subst.extend(y, TheoryFactory.createValue(1));
    assertTrue(ds.apply("O6", EquationPosition.TOPLEFT, subst));
    assertTrue(pp.getProofState().getTopEquation().toString().equals("z ≈ 7 | z = 7"));
    assertTrue(pp.getCommandHistory().get(0).equals("simplify O6 L with [x := z; y := 1]"));
  }

  @Test
  public void testSimplifyNoMatch() {
    PartialProof pp = setupProof("sum1(x) = sum2(x) | x > 0");
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    MySmtSolver solver = new MySmtSolver(true);
    Settings.smtSolver = solver;
    DeductionSimplify ds = new DeductionSimplify(pp, module);
    assertFalse(ds.apply("O3", EquationPosition.TOPLEFT));
    assertTrue(module.toString().equals(
      "The rule does not apply: constant sum2 is not instantiated by sum1.\n\n"));
    assertTrue(solver._question == null);
  }

  @Test
  public void testMissingVariablesFromSubstitution() {
    PartialProof pp = setupProof("input = 7");
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    MySmtSolver solver = new MySmtSolver(true);
    Settings.smtSolver = solver;
    DeductionSimplify ds = new DeductionSimplify(pp, module);
    assertFalse(ds.apply("O6", EquationPosition.TOPLEFT));
    assertTrue(module.toString().equals(
      "Not enough information given: " +
      "I could not determine the substitution to be used for x, y.\n\n"));
    assertTrue(solver._question == null);
  }

  @Test
  public void testSimplifyConstraintVariableNotAValue() {
    PartialProof pp = setupProof("sum1(z + 1) = iter(z + 1, 0, 0) | z ≥ 0");
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    MySmtSolver solver = new MySmtSolver(true);
    Settings.smtSolver = solver;
    DeductionSimplify ds = new DeductionSimplify(pp, module);
    assertFalse(ds.apply("O2", EquationPosition.TOPLEFT));
    assertTrue(module.toString().equals("The rule does not apply: " +
      "constraint variable x is instantiated by z + 1, which is not a value, " +
      "nor a variable in the constraint of the equation.\n\n"));
    assertTrue(solver._question == null);
  }

  @Test
  public void testSimplifyConstraintNotImplied() {
    PartialProof pp = setupProof("sum1(z) = iter(z, 0, 0) | z >= 0");
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Settings.smtSolver = new MySimpleSolver();
    DeductionSimplify ds = new DeductionSimplify(pp, module);
    assertFalse(ds.apply("O2", EquationPosition.TOPLEFT));
    assertTrue(module.toString().equals(
      "The rule does not apply: I could not prove that z ≥ 0 ⊨ z > 0.\n\n"));
  }

  @Test
  public void testOnlyNeededVariablesAfterSimplify() {
    PartialProof pp = setupProof("0 = tmp(z) | x < 0");
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    MySmtSolver solver = new MySmtSolver(false);
    Settings.smtSolver = solver;
    DeductionSimplify ds = new DeductionSimplify(pp, module);
    assertTrue(ds.apply("O7", EquationPosition.TOPRIGHT));
    Equation equation = pp.getProofState().getTopEquation();
    assertTrue(equation.toString().equals("0 ≈ 0 | x < 0"));
    assertTrue(equation.getRenaming().getReplaceable("z") == null);
  }
}

