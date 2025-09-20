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

class DeductionDisproveTest {
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
      "append(nil, ys) -> ys\n" +
      "append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n");
  }

  public PartialProof setupProof(String left, String right, String constr) {
    TRS trs = setupTRS();
    MutableRenaming renaming = new MutableRenaming(trs.queryFunctionSymbolNames());
    Variable f = TermFactory.createVar("F", CoraInputReader.readType("list -> list -> list"));
    renaming.setName(f, "F");
    Variable g = TermFactory.createVar("G", CoraInputReader.readType("list -> list"));
    renaming.setName(g, "G");
    Variable h = TermFactory.createVar("H", CoraInputReader.readType("Int -> list -> list"));
    renaming.setName(h, "H");
    Variable a = TermFactory.createVar("A", CoraInputReader.readType("Int -> Int -> Int"));
    renaming.setName(a, "A");
    Variable b = TermFactory.createVar("B", CoraInputReader.readType("Int -> Int -> Int"));
    renaming.setName(b, "B");
    Variable c = TermFactory.createVar("C", CoraInputReader.readType("Int -> Int"));
    renaming.setName(c, "C");
    Variable d = TermFactory.createVar("D", CoraInputReader.readType("Int -> Bool -> Int"));
    renaming.setName(d, "D");
    Variable u = TermFactory.createVar("U", CoraInputReader.readType("Int"));
    renaming.setName(u, "u");
    Variable v = TermFactory.createVar("V", CoraInputReader.readType("Int"));
    renaming.setName(v, "v");
    Term le = CoraInputReader.readTermAndUpdateNaming(left, renaming, trs);
    Term ri = CoraInputReader.readTermAndUpdateNaming(right, renaming, trs);
    Term co = CoraInputReader.readTermAndUpdateNaming(constr, renaming, trs);
    TermPrinter printer = new TermPrinter(Set.of());
    return new PartialProof(trs,
      FixedList.of(new EquationContext(new Equation(le, ri, co), 11, renaming)),
      lst -> printer.generateUniqueNaming(lst));
  }

  public void testDifferentConstructors() {
    PartialProof pp = setupProof("nil", "cons(x, nil)", "true");
    TRS trs = pp.getContext().getTRS();
    Term lhs = CoraInputReader.readTerm("nil", trs);
    Term rhs = CoraInputReader.readTerm("cons(x, nil)", trs);
    Pair<FunctionSymbol,FunctionSymbol> pair =
      DeductionDisprove.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
    assertTrue(pair.fst().equals(trs.lookupSymbol("nil")));
    assertTrue(pair.snd().equals(trs.lookupSymbol("cons")));
  }

  @Test
  public void testDifferentSemiconstructors() {
    PartialProof pp = setupProof("append(cons(x, nil))", "cons(y)", "x = y");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    Pair<FunctionSymbol,FunctionSymbol> pair =
      DeductionDisprove.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
    assertTrue(pair.fst().equals(trs.lookupSymbol("append")));
    assertTrue(pair.snd().equals(trs.lookupSymbol("cons")));
  }

  @Test
  public void testAritySufficient() {
    PartialProof pp = setupProof("append(cons(x, nil), z)", "cons(y, z)", "x = y");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    assertTrue(DeductionDisprove.checkDifferentSemiconstructors(lhs, rhs, pp.getContext())
      == null);
  }

  @Test
  public void testRightVariable() {
    PartialProof pp = setupProof("cons(x, z)", "z", "true");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    Pair<FunctionSymbol,FunctionSymbol> pair =
      DeductionDisprove.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
    assertTrue(pair.fst().equals(trs.lookupSymbol("cons")));
    assertTrue(pair.snd().equals(trs.lookupSymbol("nil")));
  }

  @Test
  public void testLeftVariable() {
    PartialProof pp = setupProof("F(G(nil))", "cons(x)", "true");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    Pair<FunctionSymbol,FunctionSymbol> pair =
      DeductionDisprove.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
    assertTrue(pair.fst().equals(trs.lookupSymbol("append")));
    assertTrue(pair.snd().equals(trs.lookupSymbol("cons")));

    // for G = cons(x) we still get append out, because we can make append(nil)
    lhs = lhs.queryArgument(1).queryVariable();
    pair = DeductionDisprove.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
    assertTrue(pair.fst().equals(trs.lookupSymbol("append")));
    assertTrue(pair.snd().equals(trs.lookupSymbol("cons")));
  }

  @Test
  public void testNoKnownInstance() {
    PartialProof pp = setupProof("cons(x)", "H(1)", "true");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    assertTrue(DeductionDisprove.checkDifferentSemiconstructors(lhs, rhs, pp.getContext())
      == null);
  }

  @Test
  public void testTwoVariables() {
    PartialProof pp = setupProof("H(x, y)", "y", "true");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    Pair<FunctionSymbol,FunctionSymbol> pair =
      DeductionDisprove.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
    assertTrue(pair.fst().equals(trs.lookupSymbol("cons")));
    assertTrue(pair.snd().equals(trs.lookupSymbol("nil")));
  }

  @Test
  public void testNeedCalculationSymbol() {
    PartialProof pp = setupProof("A", "B", "true");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    Pair<FunctionSymbol,FunctionSymbol> pair =
      DeductionDisprove.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
    assertTrue(!pair.fst().equals(pair.snd()));
    assertTrue(pair.fst().toCalculationSymbol() != null);
    assertTrue(pair.snd().toCalculationSymbol() != null);
    assertTrue(pair.fst().queryType().toString().equals("Int → Int → Int"));
  }

  public void testValue() {
    PartialProof pp = setupProof("u", "v", "true");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    assertTrue(DeductionDisprove.checkDifferentSemiconstructors(lhs, rhs, pp.getContext()) == null);
  }

  @Test
  public void testSameConstructor() {
    PartialProof pp = setupProof("cons(0, nil)", "cons(1, nil)", "false");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    assertTrue(DeductionDisprove.checkDifferentSemiconstructors(lhs, rhs, pp.getContext()) == null);
  }

  @Test
  public void testIncompleteState() {
    PartialProof pp = setupProof("cons(0, nil)", "nil", "true");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    // change the top equation to an incomplete one
    ProofState newstate =
      pp.getProofState().setIncomplete(pp.getProofState().getTopEquation().getIndex());
    pp.addProofStep(newstate, DeductionInduct.createStep(pp, o));
    assertTrue(DeductionDisprove.createStep(pp, o) == null);
    assertTrue(module.toString().equals(
      "DISPROVE can only be applied on complete equation contexts.\n\n"));
  }

  @Test
  public void testCreateConstructorStep() {
    PartialProof pp = setupProof("nil", "cons(0, y)", "true");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionDisprove step = DeductionDisprove.createStep(pp, o);
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().isFinalState());
    assertTrue(pp.getProofState().isContradictionState());
    assertTrue(step.commandDescription().equals("disprove"));
    step.explain(module);
    assertTrue(module.toString().equals(
      "We apply DISPROVE to E11, which succeeds because the sides can be instantiated to " +
      "distinct semi-constructor terms; respectively nil and cons(...).\n\n"));
  }

  @Test
  public void testCreateSemiconstructorStep() {
    PartialProof pp = setupProof("append(cons(x, nil))", "cons(y)", "x = y");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionDisprove step = DeductionDisprove.createStep(pp, o);
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().isFinalState());
    assertTrue(pp.getProofState().isContradictionState());
    assertTrue(step.commandDescription().equals("disprove"));
    step.explain(module);
    assertTrue(module.toString().equals(
      "We apply DISPROVE to E11, which succeeds because the sides can be instantiated to " +
      "distinct semi-constructor terms; respectively append(...) and cons(...).\n\n"));
  }

  @Test
  public void testOneSideFails() {
    PartialProof pp = setupProof("append(cons(x, nil), z)", "cons(y, z)", "x = y");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    assertTrue(DeductionDisprove.createStep(pp, o) == null);
    assertTrue(module.toString().equals("There is no substitution over the known alphabet that " +
      "would instantiate the left- and right-hand to different semi-constructor terms, nor are " +
      "the left- and right-hand side base-type theory terms.\n\n"));
  }

  @Test
  public void testAllInstances() {
    TreeSet<CalculationSymbol> set = new TreeSet<CalculationSymbol>();
    set.add(TheoryFactory.orSymbol);
    set.add(TheoryFactory.plusSymbol);
    set.add(TheoryFactory.divSymbol);
    set.add(TheoryFactory.minusSymbol);
    set.add(TheoryFactory.greaterSymbol);
    Type otype = CoraInputReader.readType("Int -> Int -> Int");
    ArrayList<Term> instances = DeductionDisprove.getAllInstances(set, otype);
    assertTrue(instances.size() == 2);
    assertTrue(instances.get(0).equals(TheoryFactory.plusSymbol));
    assertTrue(instances.get(1).equals(TheoryFactory.divSymbol));
    instances = DeductionDisprove.getAllInstances(set, CoraInputReader.readType("Int -> Int"));
    assertTrue(instances.size() == 3);
    assertTrue(instances.get(0).toString().equals("[+](X)"));
    assertTrue(instances.get(1).toString().equals("[-]"));
    assertTrue(instances.get(2).toString().equals("[/](X)"));
    instances = DeductionDisprove.getAllInstances(set, CoraInputReader.readType("Int"));
    assertTrue(instances.size() == 3);
    assertTrue(instances.get(0).toString().equals("X__1 + X__2"));
    assertTrue(instances.get(1).toString().equals("-X"));
    assertTrue(instances.get(2).toString().equals("X__1 / X__2"));
  }

  @Test
  public void testCombinations() {
    PartialProof pp = setupProof("A(x, C(y))", "B(x, 5) + C(z)", "x + y + z = 0");
    Term left = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term right = pp.getProofState().getTopEquation().getEquation().getRhs();
    ArrayList<MutableSubstitution> arr = new ArrayList<MutableSubstitution>();
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    assertTrue(DeductionDisprove.addPossibleSubstitutions(left, right, pp.getContext(),
                                                          arr, renaming, o));
    assertTrue(module.toString().equals(""));
    // number of instances for A and B: each 4 (+, *, /, %)
    // number of instances for C: 5 (+, *, /, %, -)
    // total number of combinations: 80 (4 * 4 * 5)
    assertTrue(arr.size() == 80);
    Replaceable a = renaming.getReplaceable("A");
    Replaceable b = renaming.getReplaceable("B");
    Replaceable c = renaming.getReplaceable("C");
    assertTrue(arr.get(0).get(a).toString().equals("[*]"));
    assertTrue(arr.get(0).get(b).toString().equals("[*]"));
    assertTrue(arr.get(0).get(c).toString().equals("[*](X)"));
    assertTrue(arr.get(1).get(a).toString().equals("[*]"));
    assertTrue(arr.get(1).get(b).toString().equals("[%]"));
    assertTrue(arr.get(1).get(c).toString().equals("[*](X)"));
    assertTrue(arr.get(4).get(a).toString().equals("[*]"));
    assertTrue(arr.get(4).get(b).toString().equals("[*]"));
    assertTrue(arr.get(4).get(c).toString().equals("[%](X)"));
    assertTrue(arr.get(79).get(a).toString().equals("[+]"));
    assertTrue(arr.get(79).get(b).toString().equals("[+]"));
    assertTrue(arr.get(79).get(c).toString().equals("[-]"));
  }

  @Test
  public void testCombinationsFailure() {
    PartialProof pp = setupProof("A(x, D(y, true))", "B(x, 5) + C(z)", "x + y + z = 0");
    Term left = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term right = pp.getProofState().getTopEquation().getEquation().getRhs();
    ArrayList<MutableSubstitution> arr = new ArrayList<MutableSubstitution>();
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    assertFalse(DeductionDisprove.addPossibleSubstitutions(left, right, pp.getContext(),
                                                           arr, renaming, o));
    assertTrue(module.toString().equals("There are no standard calculation symbols that could " +
      "be used to instantiate the higher-order variable D (of type Int → Bool → Int).\n\n"));
  }

  class MySmtSolver implements SmtSolver {
    Answer _answer;
    String _storage;
    MySmtSolver(Answer a) { _answer = a; _storage = null; }
    public Answer checkSatisfiability(SmtProblem problem) {
      _storage = problem.toString();
      return _answer;
    }
    public boolean checkValidity(SmtProblem problem) {
      _storage = "Validity: " + problem.toString();
      return _answer instanceof Answer.NO;
    }
  }

  @Test
  public void testFirstOrderSat() {
    PartialProof pp = setupProof("4", "y + 1", "y > 2 ∧ y < 5");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionDisprove step = DeductionDisprove.createStep(pp, o);
    Valuation val = new Valuation();
    val.setInt(1, 4);
    MySmtSolver solver = new MySmtSolver(new MySmtSolver.Answer.YES(val));
    Settings.smtSolver = solver;
    step.explain(module);
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(solver._storage.equals("(i1 >= 3) and (4 >= i1) and (3 # i1)\n"));
    assertTrue(pp.getProofState().isFinalState());
    assertTrue(pp.getProofState().isContradictionState());
    assertTrue(step.commandDescription().equals("disprove"));
    step.explain(module);
    // the explanation before and after verify are not the same
    assertTrue(module.toString().equals(
      "We apply DISPROVE to E11, which succeeds because the constraint y > 2 ∧ y < 5 ∧ " +
      "¬(4 = y + 1) is satisfiable.\n\n" +
      "We apply DISPROVE to E11, which succeeds because under the substitution [y := 4], " +
      "the constraint y > 2 ∧ y < 5 evaluates to true, while the sides of the equation can be " +
      "calculated to 4 and 5 respectively.\n\n"));
  }

  @Test
  public void testFirstOrderUnsat() {
    PartialProof pp = setupProof("4", "y + 1", "y > 2 ∧ y < 4");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionDisprove step = DeductionDisprove.createStep(pp, o);
    MySmtSolver solver = new MySmtSolver(new MySmtSolver.Answer.NO());
    Settings.smtSolver = solver;
    assertFalse(step.verifyAndExecute(pp, o));
    assertTrue(solver._storage.equals("(i1 >= 3) and (3 >= i1) and (3 # i1)\n"));
    assertFalse(pp.getProofState().isFinalState());
    assertTrue(step.commandDescription().equals("disprove"));
    assertTrue(module.toString().equals("DISPROVE cannot be applied because the constraint " +
      "y > 2 ∧ y < 4 ∧ ¬(4 = y + 1) is unsatisfiable; try DELETE instead!\n\n"));
  }

  @Test
  public void testFirstOrderMaybe() {
    PartialProof pp = setupProof("4", "y + 1", "y > 2 ∧ y < 5");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionDisprove step = DeductionDisprove.createStep(pp, o);
    Settings.smtSolver = new MySmtSolver(new MySmtSolver.Answer.MAYBE("test solver!"));
    assertFalse(step.verifyAndExecute(pp, o));
    assertTrue(module.toString().equals("Failed to apply DISPROVE, because the SMT solver " +
      "cannot prove or disprove satisfiability of y > 2 ∧ y < 5 ∧ ¬(4 = y + 1) (the solver " +
      "says \"test solver!\").\n\n"));
  }

  @Test
  public void testHigherOrderSat() {
    PartialProof pp = setupProof("A(x, 1)", "x", "x != 0");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionDisprove step = DeductionDisprove.createStep(pp, o);
    OutputModule m = OutputModule.createUnitTestModule();
    step.explain(m);
    assertTrue(m.toString().equals("We apply DISPROVE to E11, which succeeds because the " +
      "constraint x ≠ 0 ∧ ((choice = 0 ∧ ¬(x * 1 = x)) ∨ (choice = 1 ∧ ¬(x % 1 = x)) ∨ " +
      "(choice = 2 ∧ ¬(x / 1 = x)) ∨ (choice = 3 ∧ ¬(x + 1 = x))) is satisfiable.\n\n"));
    Valuation val = new Valuation();
    val.setInt(1, 0);
    val.setInt(2, 3);
    MySmtSolver solver = new MySmtSolver(new MySmtSolver.Answer.YES(val));
    Settings.smtSolver = solver;
    assertTrue(step.verify(o));
    assertTrue(solver._storage.equals("(i1 # 0) and (((i2 = 0) and (i1 * 1 # i1)) or " +
      "((i2 = 1) and (i1 % 1 # i1)) or ((i2 = 2) and (i1 / 1 # i1)) or " +
      "((i2 = 3) and (1 + i1 # i1)))\n"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply DISPROVE to E11, which succeeds because under " +
      "the substitution [A := [+], x := 0], the constraint x ≠ 0 evaluates to true, while the " +
      "sides of the equation can be calculated to 1 and 0 respectively.\n\n"));
  }

  @Test
  public void testHigherOrderUnsat() {
    PartialProof pp = setupProof("C(x)", "C(y)", "x = y");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionDisprove step = DeductionDisprove.createStep(pp, o);
    Settings.smtSolver = new MySmtSolver(new MySmtSolver.Answer.NO());
    assertFalse(step.verify(o));
    assertTrue(module.toString().equals("Failed to apply DISPROVE, because the SMT solver " +
      "cannot prove satisfiability of x = y ∧ ((choice = 0 ∧ ¬(X * x = X * y)) ∨ " +
      "(choice = 1 ∧ ¬(X % x = X % y)) ∨ (choice = 2 ∧ ¬(X / x = X / y)) ∨ " +
      "(choice = 3 ∧ ¬(X + x = X + y)) ∨ (choice = 4 ∧ ¬(-x = -y))).\n\n"));
  }
}

