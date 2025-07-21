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

class DeductionAlterRenameTest {
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
  public void testSuccessfulRenaming() {
    PartialProof pp = setupProof("iter(x, y, z) = iter(x1, u, v) | x = u + v ∨ x1 = x - 1");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    ArrayList<Pair<String,String>> names = new ArrayList<Pair<String,String>>();
    names.add(new Pair<String,String>("x", "n"));
    names.add(new Pair<String,String>("y", "x"));
    names.add(new Pair<String,String>("z", "m"));
    names.add(new Pair<String,String>("u", "k"));
    DeductionAlterRename step = DeductionAlterRename.createStep(pp, o, names);
    assertTrue(module.toString().equals(""));
    assertTrue(step.commandDescription().equals("alter rename x := n, y := x, z := m, u := k"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply ALTER to rename variables using the " +
      "substitution [x := n, y := x, z := m, u := k].\n\n"));
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , iter(n, x, m) ≈ iter(x1, k, v) | n = k + v ∨ x1 = n - 1 , •)"));
  }

  @Test
  public void testSuccessfulCircularRenaming() {
    PartialProof pp = setupProof("iter(x, y, z) = iter(a, z, x)");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    ArrayList<Pair<String,String>> names = new ArrayList<Pair<String,String>>();
    names.add(new Pair<String,String>("x", "tmp"));
    names.add(new Pair<String,String>("y", "x"));
    names.add(new Pair<String,String>("z", "y"));
    names.add(new Pair<String,String>("tmp", "z"));
    names.add(new Pair<String,String>("a", "tmp"));
    names.add(new Pair<String,String>("z", "a"));
    names.add(new Pair<String,String>("tmp", "z"));
    DeductionAlterRename step = DeductionAlterRename.createStep(pp, o, names);
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , iter(a, x, y) ≈ iter(z, y, a) , •)"));
  }

  @Test
  public void testCreationFailures() {
    PartialProof pp = setupProof("iter(x, y, z) = iter(z, y, x) | x = z");
    OutputModule module = OutputModule.createUnitTestModule();
    Optional<OutputModule> o = Optional.of(module);
    ArrayList<Pair<String,String>> names = new ArrayList<Pair<String,String>>();

    names.add(new Pair<String,String>("a", "b"));
    assertTrue(DeductionAlterRename.createStep(pp, o, names) == null);

    names.clear();
    names.add(new Pair<String,String>("y", "y"));
    assertTrue(DeductionAlterRename.createStep(pp, o, names) == null);

    names.clear();
    names.add(new Pair<String,String>("y", "z"));
    assertTrue(DeductionAlterRename.createStep(pp, o, names) == null);

    names.clear();
    names.add(new Pair<String,String>("y", "a"));
    names.add(new Pair<String,String>("z", "a"));
    assertTrue(DeductionAlterRename.createStep(pp, o, names) == null);

    names.clear();
    names.add(new Pair<String,String>("y", "f"));
    assertTrue(DeductionAlterRename.createStep(pp, o, names) == null);

    assertTrue(module.toString().equals(
      "Unknown variable name: a.\n\n" +
      "Cannot rename variable y to itself.\n\n" +
      "The name z is already in use.\n\n" +
      "The name a is already in use.\n\n" +
      "The name f is not available.\n\n"));
  }
}

