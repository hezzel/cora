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
import java.util.ArrayList;
import java.util.Optional;
import java.util.Set;

import charlie.util.Pair;
import charlie.types.TypeFactory;
import charlie.terms.*;
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

class DeductionAlterDefinitionsTest {
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
      "f :: (Int -> Int) -> unit -> Int\n" +
      "f(F, x) -> 0\n");
  }

  public PartialProof setupProof(String eqdesc) {
    TRS trs = setupTRS();
    TermPrinter printer = new TermPrinter(Set.of());
    return new PartialProof(trs, EquationParser.parseEquationList(eqdesc, trs),
      lst -> printer.generateUniqueNaming(lst));
  }

  @Test
  public void testSuccessfulAlter() {
    PartialProof pp = setupProof("sum1(x) = sum2(x) | x > 0");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenamingCopy();
    ArrayList<Pair<Pair<Variable,String>,Term>> defs =
      new ArrayList<Pair<Pair<Variable,String>,Term>>();
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    renaming.setName(y, "y1");
    Term yvalue = CoraInputReader.readTerm("x * 12 - 3", renaming, pp.getContext().getTRS());
    Variable z = TheoryFactory.createVar("z", TypeFactory.boolSort);
    Term zvalue = CoraInputReader.readTerm("y1 > 0", renaming, pp.getContext().getTRS());
    defs.add(new Pair<Pair<Variable,String>,Term>(new Pair<Variable,String>(y, "y2"), yvalue));
    defs.add(new Pair<Pair<Variable,String>,Term>(new Pair<Variable,String>(z, "z"), zvalue));
    DeductionAlterDefinitions step = DeductionAlterDefinitions.createStep(pp, o, defs).get();
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getTopEquation().getIndex() == 2);
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , sum1(x) ≈ sum2(x) | x > 0 ∧ y2 = x * 12 - 3 ∧ (z ⇔ y2 > 0) , •)"));
    assertTrue(module.toString().equals(""));
    assertTrue(step.commandDescription().toString().equals(
      "alter add y2 = x * 12 - 3, z = y2 > 0"));
    step.explain(module);
    assertTrue(module.toString().equals(
      "We apply ALTER to add y2 = x * 12 - 3 ∧ (z ⇔ y2 > 0) to the constraint of E1.\n\n"));
  }

  @Test
  public void testFailures() {
    PartialProof pp = setupProof("sum1(x) = f(F, u) | x > 0");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenamingCopy();
    ArrayList<Pair<Pair<Variable,String>,Term>> defs =
      new ArrayList<Pair<Pair<Variable,String>,Term>>();

    // no elements
    assertTrue(DeductionAlterDefinitions.createStep(pp, o, defs).isEmpty());

    // variable already exists
    Variable x = renaming.getVariable("x");
    Pair<Variable,String> xinfo = new Pair<Variable,String>(x, "x");
    defs.add(new Pair<Pair<Variable,String>,Term>(xinfo, TheoryFactory.createValue(0)));
    assertTrue(DeductionAlterDefinitions.createStep(pp, o, defs).isEmpty());
    defs.clear();

    // non-theory variable
    x = TermFactory.createVar("x", CoraInputReader.readType("unit"));
    xinfo = new Pair<Variable,String>(x, "x2");
    defs.add(new Pair<Pair<Variable,String>,Term>(xinfo, renaming.getVariable("u")));
    assertTrue(DeductionAlterDefinitions.createStep(pp, o, defs).isEmpty());
    defs.clear();

    // unknown variable in the value
    Variable y = TermFactory.createVar("y", CoraInputReader.readType("Int"));
    Pair<Variable,String> yinfo = new Pair<Variable,String>(y, "y3");
    defs.add(new Pair<Pair<Variable,String>,Term>(yinfo, CoraInputReader.readTerm("z + 1", renaming,
                                                                        pp.getContext().getTRS())));
    assertTrue(DeductionAlterDefinitions.createStep(pp, o, defs).isEmpty());
    defs.clear();

    // y itself occurs in the value
    renaming.setName(y, "y");
    defs.add(new Pair<Pair<Variable,String>,Term>(yinfo, CoraInputReader.readTerm("y + 1", renaming,
                                                                        pp.getContext().getTRS())));
    assertTrue(DeductionAlterDefinitions.createStep(pp, o, defs).isEmpty());
    defs.clear();

    // value has a higher-order subterm
    Variable F = TermFactory.createVar("F", CoraInputReader.readType("Int -> Int"));
    renaming.setName(F, "F");
    defs.add(new Pair<Pair<Variable,String>,Term>(yinfo, CoraInputReader.readTerm("F(1)", renaming,
                                                                       pp.getContext().getTRS())));
    assertTrue(DeductionAlterDefinitions.createStep(pp, o, defs).isEmpty());
    defs.clear();

    // type mismatch
    defs.add(new Pair<Pair<Variable,String>,Term>(yinfo, TheoryFactory.createValue(true)));
    assertTrue(DeductionAlterDefinitions.createStep(pp, o, defs).isEmpty());

    assertTrue(module.toString().equals(
      "Cannot introduce an empty number of definitions.\n\n" +
      "Definition for variable [x] not allowed: this variable already occurs in the equation " +
        "context.\n\n" +
      "Variable x2 has type unit, which is not a theory sort.\n\n" +
      "Unknown variable z in definition of y3.\n\n" +
      "Unknown variable y in definition of y3.\n\n" +
      "Value F(1) is not a (first-order) theory term, so does not belong in the constraint!\n\n" +
      "Type error: variable y3 has type Int while true has type Bool.\n\n"));
  }
}

