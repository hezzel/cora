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

import charlie.util.Pair;
import charlie.util.FixedList;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.*;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.Valuation;
import charlie.smt.SmtProblem;
import charlie.smt.SmtSolver;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class DeductionDisproveSemiTest {
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
    Variable b = TermFactory.createVar("b", CoraInputReader.readType("Int -> Int -> Int"));
    renaming.setName(b, "B");
    Variable u = TermFactory.createVar("u", CoraInputReader.readType("Int"));
    renaming.setName(u, "u");
    Variable v = TermFactory.createVar("u", CoraInputReader.readType("Int"));
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
      DeductionDisproveSemi.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
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
      DeductionDisproveSemi.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
    assertTrue(pair.fst().equals(trs.lookupSymbol("append")));
    assertTrue(pair.snd().equals(trs.lookupSymbol("cons")));
  }

  @Test
  public void testAritySufficient() {
    PartialProof pp = setupProof("append(cons(x, nil), z)", "cons(y, z)", "x = y");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    assertTrue(DeductionDisproveSemi.checkDifferentSemiconstructors(lhs, rhs, pp.getContext())
      == null);
  }

  @Test
  public void testRightVariable() {
    PartialProof pp = setupProof("cons(x, z)", "z", "true");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    Pair<FunctionSymbol,FunctionSymbol> pair =
      DeductionDisproveSemi.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
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
      DeductionDisproveSemi.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
    assertTrue(pair.fst().equals(trs.lookupSymbol("append")));
    assertTrue(pair.snd().equals(trs.lookupSymbol("cons")));

    // for G = cons(x) we still get append out, because we can make append(nil)
    lhs = lhs.queryArgument(1).queryVariable();
    pair = DeductionDisproveSemi.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
    assertTrue(pair.fst().equals(trs.lookupSymbol("append")));
    assertTrue(pair.snd().equals(trs.lookupSymbol("cons")));
  }

  @Test
  public void testNoKnownInstance() {
    PartialProof pp = setupProof("cons(x)", "H(1)", "true");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    assertTrue(DeductionDisproveSemi.checkDifferentSemiconstructors(lhs, rhs, pp.getContext())
      == null);
  }

  @Test
  public void testTwoVariables() {
    PartialProof pp = setupProof("H(x, y)", "y", "true");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    Pair<FunctionSymbol,FunctionSymbol> pair =
      DeductionDisproveSemi.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
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
      DeductionDisproveSemi.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
    assertTrue(!pair.fst().equals(pair.snd()));
    assertTrue(pair.fst().toCalculationSymbol() != null);
    assertTrue(pair.snd().toCalculationSymbol() != null);
    assertTrue(pair.fst().queryType().toString().equals("Int → Int → Int"));
  }

  @Test
  public void testNeedValue() {
    PartialProof pp = setupProof("u", "v", "true");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    Pair<FunctionSymbol,FunctionSymbol> pair =
      DeductionDisproveSemi.checkDifferentSemiconstructors(lhs, rhs, pp.getContext());
    assertTrue(!pair.fst().equals(pair.snd()));
    assertTrue(pair.fst().isValue());
    assertTrue(pair.snd().isValue());
    assertTrue(pair.fst().queryType().toString().equals("Int"));
  }

  @Test
  public void testSameConstructor() {
    PartialProof pp = setupProof("cons(0, nil)", "cons(1, nil)", "false");
    TRS trs = pp.getContext().getTRS();
    Term lhs = pp.getProofState().getTopEquation().getEquation().getLhs();
    Term rhs = pp.getProofState().getTopEquation().getEquation().getRhs();
    assertTrue(DeductionDisproveSemi.checkDifferentSemiconstructors(lhs, rhs, pp.getContext()) == null);
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
    DeductionDisproveSemi step = DeductionDisproveSemi.createStep(pp, o);
    assertFalse(step.verify(o));
    assertTrue(module.toString().equals(
      "DISPROVE can only be applied on complete equation contexts.\n\n"));
  }

  @Test
  public void testCreateConstructorStep() {
    PartialProof pp = setupProof("nil", "cons(0, y)", "true");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    DeductionDisproveSemi step = DeductionDisproveSemi.createStep(pp, o);
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
    DeductionDisproveSemi step = DeductionDisproveSemi.createStep(pp, o);
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
    assertTrue(DeductionDisproveSemi.createStep(pp, o) == null);
    assertTrue(module.toString().equals("There is no substitution over the known alphabet that " +
      "would instantiate the left- and right-hand to different semi-constructor terms.\n\n"));
  }
}

