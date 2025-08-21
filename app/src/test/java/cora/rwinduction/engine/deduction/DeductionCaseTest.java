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
import java.util.List;
import java.util.Set;
import java.util.Optional;

import charlie.util.FixedList;
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.TermFactory;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.engine.*;

class DeductionCaseTest {
  private TRS trs = CoraInputReader.readTrsFromString(
    "iter :: Int -> Int -> Int -> Int\n" +
    "iter(x, i, z) -> z | i > x\n" +
    "iter(x, i, z) -> iter(x, i+1, z+i) | i <= x\n" +
    "nil :: list\n" +
    "cons :: Int -> list -> list\n" +
    "append :: list -> list -> list\n" +
    "append(nil, xs) -> xs\n" +
    "append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n" +
    "isempty :: list -> Bool\n" +
    "isempty(nil) -> true\n" +
    "isempty(cons(x,xs)) -> false\n" +
    "size :: list -> Int\n" +
    "size(nil) -> 0\n" +
    "size(cons(x,xs)) -> size(xs) + 1\n" +
    "f :: String -> Bool\n" +
    "g :: (| Int , Bool |) -> (| Int, list |)\n" +
    "h :: (| Int , list |) -> A\n" +
    "map :: (Int -> Int) -> list -> list\n" +
    "map(F, nil) -> nil\n" +
    "map(F, cons(x, xs)) -> cons(F(x), map(F, xs))\n"
    );

  public PartialProof setupProof(String eq, OutputModule module) {
    return new PartialProof(trs,
      EquationParser.parseEquationList(eq, trs),
      lst -> module.generateUniqueNaming(lst));
  }

  public PartialProof setupProof(String leftgeq, String lhs, String rhs, String constr,
                                 String rightgeq, OutputModule module) {
    MutableRenaming renaming = new MutableRenaming(trs.queryFunctionSymbolNames());
    Term lg = CoraInputReader.readTermAndUpdateNaming(leftgeq, renaming, trs);
    Term le = CoraInputReader.readTermAndUpdateNaming(lhs, renaming, trs);
    Term ri = CoraInputReader.readTermAndUpdateNaming(rhs, renaming, trs);
    Term co = CoraInputReader.readTermAndUpdateNaming(constr, renaming, trs);
    Term rg = CoraInputReader.readTermAndUpdateNaming(rightgeq, renaming, trs);
    EquationContext ec = new EquationContext(lg, new Equation(le, ri, co), rg, 5, renaming);
    return new PartialProof(trs, FixedList.of(ec), lst -> module.generateUniqueNaming(lst));
  }

  @Test
  public void testSuccessfulBooleanStep() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof pp = setupProof("iter(x,i,z) = iter(x+1,i-1,z*i) | i > 0", module);
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term t = CoraInputReader.readTerm("i > x", renaming, trs);
    DeductionCase step = DeductionCase.createStep(pp, o, t);
    assertTrue(step.commandDescription().equals("case i > x"));
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(module.toString().equals(""));
    FixedList<EquationContext> eqs = pp.getProofState().getEquations();
    assertTrue(eqs.size() == 2);
    assertTrue(eqs.get(0).toString().equals(
      "E2: (• , iter(x, i, z) ≈ iter(x + 1, i - 1, z * i) | i > 0 ∧ i > x , •)"));
    assertTrue(eqs.get(1).toString().equals(
      "E3: (• , iter(x, i, z) ≈ iter(x + 1, i - 1, z * i) | i > 0 ∧ ¬(i > x) , •)"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply CASE on the constraint i > x.\n\n"));
  }

  @Test
  public void testSuccessfulIntegerStep() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof pp = setupProof("iter(x,i,z)", "iter(x,i1,z1)", "iter(x-1,i1+1,z1*i)",
      "i > 0 ∧ i1 = i+1 ∧ z1 = z+i", "iter(x,z,i)", module);
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term t = CoraInputReader.readTerm("i1 - z", renaming, trs);
    DeductionCase step = DeductionCase.createStep(pp, o, t);
    assertTrue(step.commandDescription().equals("case i1 - z"));
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(module.toString().equals(""));
    FixedList<EquationContext> eqs = pp.getProofState().getEquations();
    assertTrue(eqs.size() == 3);
    assertTrue(eqs.get(0).toString().equals(
      "E6: (iter(x, i, z) , iter(x, i1, z1) ≈ iter(x - 1, i1 + 1, z1 * i) | i > 0 ∧ " +
        "i1 = i + 1 ∧ z1 = z + i ∧ i1 - z > 0 , iter(x, z, i))"));
    assertTrue(eqs.get(1).toString().equals(
      "E7: (iter(x, i, z) , iter(x, i1, z1) ≈ iter(x - 1, i1 + 1, z1 * i) | i > 0 ∧ " +
        "i1 = i + 1 ∧ z1 = z + i ∧ i1 - z = 0 , iter(x, z, i))"));
    assertTrue(eqs.get(2).toString().equals(
      "E8: (iter(x, i, z) , iter(x, i1, z1) ≈ iter(x - 1, i1 + 1, z1 * i) | i > 0 ∧ " +
        "i1 = i + 1 ∧ z1 = z + i ∧ i1 - z < 0 , iter(x, z, i))"));
    step.explain(module);
    assertTrue(module.toString().equals("We apply CASE on the value of i1 - z.\n\n"));
  }

  @Test
  public void testSuccessfulConstructorStep() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof pp = setupProof("append(xs, ys)", "append(x, xs)", "append(y, ys)",
      "true", "append(ys, xs)", module);
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term t = (Variable)renaming.getReplaceable("xs");
    DeductionCase step = DeductionCase.createStep(pp, o, t);
    assertTrue(step.commandDescription().equals("case xs"));
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(module.toString().equals(""));
    FixedList<EquationContext> eqs = pp.getProofState().getEquations();
    assertTrue(eqs.size() == 2);
    assertTrue(eqs.get(0).toString().equals("E6: (append(cons(xs1, xs2), ys) , " +
      "append(x, cons(xs1, xs2)) ≈ append(y, ys) , append(ys, cons(xs1, xs2)))"));
    assertTrue(eqs.get(1).toString().equals("E7: (append(nil, ys) , " +
      "append(x, nil) ≈ append(y, ys) , append(ys, nil))"));
  }

  @Test
  public void testSuccessfulTupleStep() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof pp = setupProof("g(x) = g((| y, true |)) | y > 0", module);
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term t = (Variable)renaming.getReplaceable("x");
    DeductionCase step = DeductionCase.createStep(pp, o, t);
    assertTrue(step.commandDescription().equals("case x"));
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(module.toString().equals(""));
    assertTrue(pp.getProofState().getEquations().size() == 1);
    assertTrue(pp.getProofState().getTopEquation().toString().equals(
      "E2: (• , g(⦇x1, x2⦈) ≈ g(⦇y, true⦈) | y > 0 , •)"));
  }

  @Test
  public void testSuccessfulTupleConstructorStep() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof pp = setupProof("h(x)", "h(x)", "h((| y, zs |))", "y > 0", "h(x)", module);
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term t = (Variable)renaming.getReplaceable("x");
    DeductionCase step = DeductionCase.createStep(pp, o, t);
    assertTrue(step.commandDescription().equals("case x"));
    assertTrue(step.verifyAndExecute(pp, o));
    assertTrue(module.toString().equals(""));
    FixedList<EquationContext> eqs = pp.getProofState().getEquations();
    assertTrue(eqs.size() == 2);
    assertTrue(eqs.get(0).toString().equals(
      "E6: (h(g(x1)) , h(g(x1)) ≈ h(⦇y, zs⦈) | y > 0 , h(g(x1)))"));
    assertTrue(eqs.get(1).toString().equals(
      "E7: (h(⦇x1, x2⦈) , h(⦇x1, x2⦈) ≈ h(⦇y, zs⦈) | y > 0 , h(⦇x1, x2⦈))"));
  }

  @Test
  public void testFailedBooleanStep() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof pp = setupProof("append(x) = append(y)", module);
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term t = CoraInputReader.readTerm("isempty(x)", renaming, trs);
    assertTrue(DeductionCase.createStep(pp, o, t) == null);
    assertTrue(module.toString().equals("Cannot do case analysis on isempty(x): this is a " +
      "boolean term, but not a first-order theory term, so it cannot be added to the " +
      "constraint.\n\n"));
  }

  @Test
  public void testFailedIntegerStep() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof pp = setupProof("append(x) = append(y)", module);
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term t = CoraInputReader.readTerm("size(x) + 2", renaming, trs);
    assertTrue(DeductionCase.createStep(pp, o, t) == null);
    assertTrue(module.toString().equals("Cannot do case analysis on size(x) + 2: this is an " +
      "integer term, but not a first-order theory term, so it cannot be included in the " +
      "constraint.\n\n"));
  }

  @Test
  public void testFailVerificationForCaseOnBooleanVariable() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof pp = setupProof("append(x) = append(y)", module);
    Optional<OutputModule> o = Optional.of(module);
    Term t = TermFactory.createVar("mybool", CoraInputReader.readType("Bool"));
    DeductionCase step = DeductionCase.createStep(pp, o, t);
    assertFalse(step.verify(o));
    assertTrue(module.toString().equals("Cannot do a case analysis on a variable that does not " +
      "occur in the equation.\n\n"));
  }

  @Test
  public void testFailVerificationForIntegerExpression() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof pp = setupProof("iter(x,i,z) = iter(x+1,i-1,z*i) | i > 0", module);
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term t = CoraInputReader.readTerm("i - xx", renaming, trs);
    DeductionCase step = DeductionCase.createStep(pp, o, t);
    assertTrue(step.commandDescription().equals("case i - xx"));
    assertFalse(step.verify(o));
    assertTrue(module.toString().equals("Unknown variable in case term: \"i - xx\".\n\n"));
  }

  @Test
  public void testCaseOnString() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof pp = setupProof("f(x) = f(y) | x = y", module);
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term t = (Variable)renaming.getReplaceable("x");
    assertTrue(DeductionCase.createStep(pp, o, t) == null);
    assertTrue(module.toString().equals(
      "Cannot do a case analysis on a variable of type String.\n\n"));
  }

  @Test
  public void testCaseOnArrow() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof pp = setupProof("map(F, nil) = map(F, append(nil, nil))", module);
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term t = (Variable)renaming.getReplaceable("F");
    assertTrue(DeductionCase.createStep(pp, o, t) == null);
    assertTrue(module.toString().equals(
      "Cannot do a case analysis on a variable of type Int → Int.\n\n"));
  }

  @Test
  public void testCaseOnComplexNonTheoryTerm() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof pp = setupProof("append(append(x, y), z) = append(x, append(y, z))", module);
    Optional<OutputModule> o = Optional.of(module);
    Renaming renaming = pp.getProofState().getTopEquation().getRenaming();
    Term t = CoraInputReader.readTerm("append(x, y)", renaming, trs);
    assertTrue(DeductionCase.createStep(pp, o, t) == null);
    assertTrue(module.toString().equals(
      "Cannot do a case analysis on append(x, y): this term is not a constraint or integer " +
      "theory term, nor a variable (it has type list).\n\n"));
  }
}

