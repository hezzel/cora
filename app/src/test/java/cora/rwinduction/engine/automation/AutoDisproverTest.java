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

package cora.rwinduction.engine.automation;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.Optional;

import charlie.util.FixedList;
import charlie.types.Type;
import charlie.terms.replaceable.*;
import charlie.terms.*;
import charlie.substitution.Substitution;
import charlie.substitution.MutableSubstitution;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.*;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;
import cora.rwinduction.engine.deduction.DeductionInduct;

class AutoDisproveTest {
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

  @Test
  public void testFirstOrderSat() {
    TRS trs = setupTRS();
    MutableRenaming renaming = new MutableRenaming(trs.queryFunctionSymbolNames());
    Term left = CoraInputReader.readTermAndUpdateNaming("4", renaming, trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("y + 1", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("y > 2 ∧ y < 5", renaming, trs);
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Valuation val = new Valuation();
    val.setInt(1, 4);
    Settings.smtSolver = new ProgrammableSmtSolver(
      "(i1 >= 3) and (4 >= i1) and (3 # i1)", new SmtSolver.Answer.YES(val));
    Substitution subst =
      AutoDisprover.findContradictingTheorySubstitution(left, right, constraint, o, renaming);
    assertTrue(subst.domain().size() == 1);
    assertTrue(subst.get(renaming.getReplaceable("y")).equals(left));
    assertTrue(module.toString().equals(""));
  }

  @Test
  public void testFirstOrderUnsat() {
    TRS trs = setupTRS();
    MutableRenaming renaming = new MutableRenaming(trs.queryFunctionSymbolNames());
    Term left = CoraInputReader.readTermAndUpdateNaming("4", renaming, trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("y + 1", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("y > 2 ∧ y < 4", renaming, trs);
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);

    Settings.smtSolver = new ProgrammableSmtSolver("(i1 >= 3) and (3 >= i1) and (3 # i1)",
                                                   new SmtSolver.Answer.NO());
    assertTrue(AutoDisprover.findContradictingTheorySubstitution(left, right, constraint,
               o, renaming) == null);
    assertTrue(module.toString().equals("DISPROVE cannot be applied because y > 2 ∧ y < 4 ∧ " +
      "¬(4 = y + 1) is unsatisfiable; try EQ-DELETE instead!\n\n"));

    module = OutputModule.createUnitTestModule();
    o = Optional.of(module);
    Settings.smtSolver = new ProgrammableSmtSolver("(i1 >= 3) and (3 >= i1) and (3 # i1)",
                                                   new SmtSolver.Answer.MAYBE("test solver!"));
    assertTrue(AutoDisprover.findContradictingTheorySubstitution(left, right, constraint,
               o, renaming) == null);
    assertTrue(module.toString().equals("Failed to apply DISPROVE, because the SMT solver " +
      "cannot prove or disprove satisfiability of y > 2 ∧ y < 4 ∧ ¬(4 = y + 1) (the solver " +
      "says \"test solver!\").\n\n"));
  }

  @Test
  public void testAllInstances() {
    Type otype = CoraInputReader.readType("Int -> Int -> Int");
    ArrayList<Term> instances = AutoDisprover.getAllInstances(otype);
    assertTrue(instances.size() == 4);
    assertTrue(instances.contains(TheoryFactory.plusSymbol));
    assertTrue(instances.contains(TheoryFactory.timesSymbol));
    assertTrue(instances.contains(TheoryFactory.divSymbol));
    assertTrue(instances.contains(TheoryFactory.modSymbol));
    instances = AutoDisprover.getAllInstances(CoraInputReader.readType("Int -> Int"));
    TreeSet<String> elems = new TreeSet<String>();
    for (Term t : instances) elems.add(t.toString());
    assertTrue(elems.contains("[+](X)"));
    assertTrue(elems.contains("[-]"));
    assertTrue(elems.contains("[/](X)"));
    instances = AutoDisprover.getAllInstances(CoraInputReader.readType("Int"));
    assertTrue(instances.size() == 5);
    elems.clear();
    for (Term t : instances) elems.add(t.toString());
    assertTrue(elems.contains("X__1 + X__2"));
    assertTrue(elems.contains("X__1 * X__2"));
    assertTrue(elems.contains("-X"));
  }
  
  class NoSolver implements SmtSolver {
    private ArrayList<String> _storage;
    public NoSolver() { _storage = new ArrayList<String>(); }
    public Answer checkSatisfiability(SmtProblem problem) {
      _storage.add(problem.toString());
      return new Answer.NO();
    }
    public boolean checkValidity(SmtProblem problem) {
      assertTrue(false, "Asked for validity in NoSolver");
      return false;
    }
  }

  @Test
  public void testCombinations() {
    TRS trs = setupTRS();
    MutableRenaming renaming = new MutableRenaming(trs.queryFunctionSymbolNames());
    Variable a = TermFactory.createVar("A", CoraInputReader.readType("Int -> Int -> Int"));
    renaming.setName(a, "A");
    Variable b = TermFactory.createVar("B", CoraInputReader.readType("Int -> Int -> Int"));
    renaming.setName(b, "B");
    Variable c = TermFactory.createVar("C", CoraInputReader.readType("Int -> Int"));
    renaming.setName(c, "C");
    Term left = CoraInputReader.readTermAndUpdateNaming("A(x, C(y))", renaming, trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("B(x, 5) + C(z)", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x + y + z = 0", renaming, trs);
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);

    NoSolver solver = new NoSolver();
    Settings.smtSolver = solver;
    assertTrue(AutoDisprover.findContradictingTheorySubstitution(left, right, constraint, o,
                                                                 renaming) == null);
    assertTrue(module.toString().equals("No substitution could be found that makes x + y + z = 0 " +
      "true and A(x, C(y)) ≠ B(x, 5) + C(z).  If such a substitution does exist, please supply " +
      "it manually.\n\n"));
    assertTrue(solver._storage.size() == 80); // 4 * 5 * 4
    assertTrue(solver._storage.get(0).equals( // A := [+], C := [+](?), B := [+]
      "(i1 + i2 + i3 = 0) and (i1 + i4 + i2 # 5 + i1 + i4 + i3)\n"));
    assertTrue(solver._storage.get(1).equals( // A := [+], C := [+](?), B := [*]
      "(i1 + i2 + i3 = 0) and (i1 + i4 + i2 # i1 * 5 + i4 + i3)\n"));
    assertTrue(solver._storage.get(2).equals( // A := [+], C := [+](?), B := [/]
      "(i1 + i2 + i3 = 0) and (i1 + i4 + i2 # i1 / 5 + i4 + i3)\n"));
    assertTrue(solver._storage.get(4).equals( // A := [+], C := [*](?), B := [+]
      "(i1 + i2 + i3 = 0) and (i1 + i4 * i2 # 5 + i1 + i4 * i3)\n"));
    assertTrue(solver._storage.get(29).equals( // A := [*], C := [-], B := [*]
      "(i1 + i2 + i3 = 0) and (i1 * -1 * i2 + i3 # i1 * 5)\n"));
  }

  @Test
  public void testNoInstanceFailure() {
    TRS trs = setupTRS();
    MutableRenaming renaming = new MutableRenaming(trs.queryFunctionSymbolNames());
    Variable a = TermFactory.createVar("A", CoraInputReader.readType("Int -> Int -> Int"));
    renaming.setName(a, "A");
    Variable b = TermFactory.createVar("B", CoraInputReader.readType("Int -> Int -> Int"));
    renaming.setName(b, "B");
    Variable c = TermFactory.createVar("C", CoraInputReader.readType("Int -> Int"));
    renaming.setName(c, "C");
    Variable d = TermFactory.createVar("D", CoraInputReader.readType("Int -> Bool -> Int"));
    renaming.setName(d, "D");
    Term l = CoraInputReader.readTermAndUpdateNaming("A(x, D(y, true))", renaming, trs);
    Term r = CoraInputReader.readTermAndUpdateNaming("B(x, 5) + C(z)", renaming, trs);
    Term co = CoraInputReader.readTermAndUpdateNaming("x + y + z = 0", renaming, trs);
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);

    Settings.smtSolver = null;
    assertTrue(AutoDisprover.findContradictingTheorySubstitution(l, r, co, o, renaming) == null);
    assertTrue(module.toString().equals("There are no standard calculation symbols that could " +
      "be used to instantiate the higher-order variable D (of type Int → Bool → Int).\n\n"));
  }

  @Test
  public void testFindInstance() {
    TRS trs = setupTRS();
    MutableRenaming renaming = new MutableRenaming(trs.queryFunctionSymbolNames());
    Variable a = TermFactory.createVar("A", CoraInputReader.readType("Int -> Int -> Int"));
    renaming.setName(a, "A");
    Term left = CoraInputReader.readTermAndUpdateNaming("A(x, 1)", renaming, trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("x", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x != 0", renaming, trs);
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);

    Valuation val = new Valuation();
    val.setInt(1, 0);
    val.setInt(2, 3);
    Settings.smtSolver =
      new ProgrammableSmtSolver("(i1 # 0) and (1 + i1 # i1)", new SmtSolver.Answer.YES(val));

    Substitution substitution =
      AutoDisprover.findContradictingTheorySubstitution(left, right, constraint, o, renaming);
    assertTrue(substitution.domain().size() == 2);
    assertTrue(substitution.get(renaming.getReplaceable("A")).toString().equals("[+]"));
    assertTrue(substitution.get(renaming.getReplaceable("x")).toString().equals("0"));
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

  @Test
  public void testHigherOrderSat() {
    PartialProof pp = setupProof("A(x, 1)", "x", "x != 5");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Valuation val = new Valuation();
    val.setInt(1, 0);
    val.setInt(2, 3);
    Settings.smtSolver =
      new ProgrammableSmtSolver("(i1 # 5) and (1 + i1 # i1)", new SmtSolver.Answer.YES(val));
    DeductionStep step = AutoDisprover.createStep(pp, o);
    assertTrue(step.verify(o));
    step.explain(module);
    assertTrue(module.toString().equals("We apply DISPROVE to E11, which succeeds because under " +
      "the substitution [A := [+], x := 0], the constraint x ≠ 5 evaluates to true, while the " +
      "sides of the equation can be calculated to 1 and 0 respectively.\n\n"));
  }

  @Test
  public void testHigherOrderUnsat() {
    PartialProof pp = setupProof("C(x)", "C(y)", "x = y");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Settings.smtSolver = new NoSolver();
    assertTrue(AutoDisprover.createTheoryStep(pp, o) == null);
    assertTrue(module.toString().equals("No substitution could be found that makes x = y true " +
      "and C(x) ≠ C(y).  If such a substitution does exist, please supply it manually.\n\n"));
  }

  @Test
  public void testNeedCalculationSymbol() {
    PartialProof pp = setupProof("A", "B", "true");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Settings.smtSolver = null;
    DeductionStep step = AutoDisprover.createStep(pp, o);
    assertTrue(step.commandDescription().equals("disprove root"));
  }

  @Test
  public void testValue() {
    PartialProof pp = setupProof("u", "v", "true");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Valuation val = new Valuation();
    val.setInt(1, 1);
    val.setInt(2, 2);
    Settings.smtSolver = new ProgrammableSmtSolver("i1 # i2", new SmtSolver.Answer.YES(val));
    DeductionStep step = AutoDisprover.createStep(pp, o);
    assertTrue(step.commandDescription().equals("disprove theory with [u := 1, v := 2]"));
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
    assertTrue(AutoDisprover.createStep(pp, o) == null);
    assertTrue(module.toString().equals(
      "DISPROVE can only be applied on complete equation contexts.\n\n"));
  }
}

