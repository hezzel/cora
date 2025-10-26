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

class DeductionDisproveRootTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "sum :: Int -> Int\n" +
      "sum(x) -> 0 | x <= 0\n" +
      "sum(x) -> x + sum(x-1) | x > 0\n" +
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
  public void testDifferentConstructors() {
    PartialProof pp = setupProof("nil", "cons(x, nil)", "true");
    TRS trs = pp.getContext().getTRS();
    Term lhs = CoraInputReader.readTerm("nil", trs);
    Term rhs = CoraInputReader.readTerm("cons(x, nil)", trs);
    Pair<FunctionSymbol,FunctionSymbol> pair =
      DeductionDisproveRoot.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
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
      DeductionDisproveRoot.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
    assertTrue(pair.fst().equals(trs.lookupSymbol("append")));
    assertTrue(pair.snd().equals(trs.lookupSymbol("cons")));
  }

  @Test
  public void testAritySufficient() {
    PartialProof pp = setupProof("append(cons(x, nil), z)", "cons(y, z)", "x = y");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    assertTrue(DeductionDisproveRoot.checkDifferentSemiconstructors(lhs, rhs, pp.getContext())
      == null);
  }

  @Test
  public void testRightVariable() {
    PartialProof pp = setupProof("cons(x, z)", "z", "true");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    Pair<FunctionSymbol,FunctionSymbol> pair =
      DeductionDisproveRoot.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
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
      DeductionDisproveRoot.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
    assertTrue(pair.fst().equals(trs.lookupSymbol("append")));
    assertTrue(pair.snd().equals(trs.lookupSymbol("cons")));

    // for G = cons(x) we still get append out, because we can make append(nil)
    lhs = lhs.queryArgument(1).queryVariable();
    pair = DeductionDisproveRoot.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
    assertTrue(pair.fst().equals(trs.lookupSymbol("append")));
    assertTrue(pair.snd().equals(trs.lookupSymbol("cons")));
  }

  @Test
  public void testNoKnownInstance() {
    PartialProof pp = setupProof("cons(x)", "H(1)", "true");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    assertTrue(DeductionDisproveRoot.checkDifferentSemiconstructors(lhs, rhs, pp.getContext())
      == null);
  }

  @Test
  public void testTwoVariables() {
    PartialProof pp = setupProof("H(x, y)", "y", "true");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    Pair<FunctionSymbol,FunctionSymbol> pair =
      DeductionDisproveRoot.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
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
      DeductionDisproveRoot.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
    assertTrue(!pair.fst().equals(pair.snd()));
    assertTrue(pair.fst().toCalculationSymbol() != null);
    assertTrue(pair.snd().toCalculationSymbol() != null);
    assertTrue(pair.fst().queryType().toString().equals("Int → Int → Int"));
  }

  @Test
  public void testValue() {
    PartialProof pp = setupProof("u", "v", "true");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    // while it's theoretically possible, in practice we want to handle this as theory
    assertTrue(DeductionDisproveRoot.checkDifferentSemiconstructors(lhs, rhs, pp.getContext())
      == null);
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(DeductionDisproveRoot.createStep(pp, Optional.of(module)) == null);
    assertTrue(module.toString().equals("This case should be handled using DISPROVE THEORY " +
      "rather than DISPROVE ROOT.\n\n"));
  }

  @Test
  public void testSameConstructor() {
    PartialProof pp = setupProof("cons(0, nil)", "cons(1, nil)", "false");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    assertTrue(DeductionDisproveRoot.checkDifferentSemiconstructors(lhs, rhs, pp.getContext())
      == null);
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(DeductionDisproveRoot.createStep(pp, Optional.of(module)) == null);
    assertTrue(module.toString().equals("Both sides have the same root symbol.\n\n"));
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
    assertTrue(DeductionDisproveRoot.createStep(pp, o) == null);
    assertTrue(module.toString().equals(
      "DISPROVE can only be applied on complete equation contexts.\n\n"));
  }

  @Test
  public void testCreateConstructorStep() {
    PartialProof pp = setupProof("nil", "cons(0, y)", "true");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionDisproveRoot step = DeductionDisproveRoot.createStep(pp, o);
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().isFinalState());
    assertTrue(pp.getProofState().isContradictionState());
    assertTrue(step.commandDescription().equals("disprove root"));
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
    DeductionDisproveRoot step = DeductionDisproveRoot.createStep(pp, o);
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().isFinalState());
    assertTrue(pp.getProofState().isContradictionState());
    assertTrue(step.commandDescription().equals("disprove root"));
    step.explain(module);
    assertTrue(module.toString().equals(
      "We apply DISPROVE to E11, which succeeds because the sides can be instantiated to " +
      "distinct semi-constructor terms; respectively append(...) and cons(...).\n\n"));
  }

  @Test
  public void testOneSideReducible() {
    PartialProof pp = setupProof("append(cons(x, nil), z)", "cons(y, z)", "x = y");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    assertTrue(DeductionDisproveRoot.createStep(pp, o) == null);
    assertTrue(module.toString().equals("Disprove can only be applied (on non-theory terms) " +
      "when neither side is a functional term with enough arguments to apply a rule.\n\n"));
  }
}

