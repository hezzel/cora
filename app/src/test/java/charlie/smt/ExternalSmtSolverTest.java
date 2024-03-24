/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.smt;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import charlie.smt.SmtSolver.Answer;

public class ExternalSmtSolverTest {
  // @Test
  // NOTE: @Test removed because we don't want to be writing files at every compile
  public void testSimpleValidityCheck() {
    ExternalSmtSolver solver = new ExternalSmtSolver();
    SmtProblem problem = new SmtProblem();
    // x > 1 => x > 0 is valid
    IVar x = problem.createIntegerVariable();
    Constraint gr1 = new Greater(x, new IValue(1));
    Constraint gr0 = new Greater(x, new IValue(0));
    problem.requireImplication(gr1, gr0);
    assertTrue(solver.checkValidity(problem));
    // x > 0 => x > 1 is not valid
    problem.clear();
    problem.requireImplication(gr0, gr1);
    assertFalse(solver.checkValidity(problem));
  }

  // @Test
  // NOTE: @Test removed because we don't want to be writing files at every compile
  public void testSimpleSatisfiabilityCheck() {
    ExternalSmtSolver solver = new ExternalSmtSolver();
    SmtProblem problem = new SmtProblem();
    // x ∧ z < 0 ∧ y > 12 ∧ y = z
    BVar x = problem.createBooleanVariable();
    IVar y = problem.createIntegerVariable();
    IVar z = problem.createIntegerVariable();
    problem.createBooleanVariable();
    Constraint le = new Greater(new IValue(0), z);
    Constraint gr = new Greater(y, new IValue(12));
    Constraint eq = new Equal(y, z);
    problem.require(new Conjunction(x, new Conjunction(le, new Conjunction(gr, eq))));
    assertTrue(solver.checkSatisfiability(problem) instanceof Answer.NO);
    problem.clear();
    // x ∧ z < 10 ∧ (y > 12 ∨ y = z)
    problem.require(new Conjunction(x, new Conjunction(le, new Disjunction(gr, eq))));
    Answer a = solver.checkSatisfiability(problem);
    if (a instanceof Answer.YES(Valuation v)) {
      assertTrue(v.queryAssignment(x));
      assertTrue(v.queryAssignment(z) < 0);
      assertTrue(v.queryAssignment(y) > 12 || v.queryAssignment(y) == v.queryAssignment(z));
      System.out.println(v);
    }
    else assertTrue(false);
    problem.clear();
    // x ∧ z > u, where u is a variable NOT in the problem
    IVar u = new IVar(100);
    problem.require(new Conjunction(x, new Greater(z, u)));
    a = solver.checkSatisfiability(problem);
    if (a instanceof Answer.MAYBE(String reason)) {
      System.out.println(reason);
    }
    else assertTrue(false);
    problem.clear();
  }
}

