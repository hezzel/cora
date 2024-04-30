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

package charlie.solvesmt;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import charlie.smt.*;
import charlie.smt.SmtSolver.Answer;

public class ExternalSmtSolversTest {
  public void testSimpleValidityCheck(SmtSolver solver) {
    SmtProblem problem = new SmtProblem();
    // x > 1 => x > 0 is valid
    IVar x = problem.createIntegerVariable();
    Constraint gr1 = SmtFactory.createGreater(x, SmtFactory.createValue(1));
    Constraint gr0 = SmtFactory.createGreater(x, SmtFactory.createValue(0));
    problem.requireImplication(gr1, gr0);
    assertTrue(solver.checkValidity(problem));
    // x > 0 => x > 1 is not valid
    problem.clear();
    problem.requireImplication(gr0, gr1);
    assertFalse(solver.checkValidity(problem));
  }

  @Test
  public void testSimpleValidityCheckForProcessSolver() {
    testSimpleValidityCheck(new ProcessSmtSolver());
  }

  @Test
  public void testSimpleValidityCheckForExternalSolver() {
    testSimpleValidityCheck(new ExternalSmtSolver());
  }

  @Test
  public void testSimpleSatisfiabilityCheck() {
    ProcessSmtSolver solver = new ProcessSmtSolver();
    SmtProblem problem = new SmtProblem();
    // x ∧ z < 0 ∧ y > 12 ∧ y = z
    BVar x = problem.createBooleanVariable();
    IVar y = problem.createIntegerVariable();
    IVar z = problem.createIntegerVariable();
    problem.createBooleanVariable();
    Constraint le = SmtFactory.createGreater(SmtFactory.createValue(0), z);
    Constraint gr = SmtFactory.createGreater(y, SmtFactory.createValue(12));
    Constraint eq = SmtFactory.createEqual(y, z);
    problem.require(SmtFactory.createConjunction(x, SmtFactory.createConjunction(le,
      SmtFactory.createConjunction(gr, eq))));
    assertTrue(solver.checkSatisfiability(problem) instanceof Answer.NO);
    problem.clear();
    // x ∧ z < 10 ∧ (y > 12 ∨ y = z)
    problem.require(SmtFactory.createConjunction(x, SmtFactory.createConjunction(le,
      SmtFactory.createDisjunction(gr, eq))));
    Answer a = solver.checkSatisfiability(problem);
    if (a instanceof Answer.YES(Valuation v)) {
      assertTrue(v.queryAssignment(x));
      assertTrue(v.queryAssignment(z) < 0);
      assertTrue(v.queryAssignment(y) > 12 || v.queryAssignment(y) == v.queryAssignment(z));
      //System.out.println(v);
    }
    else assertTrue(false);
    problem.clear();
    // x ∧ z > u, where u is a variable NOT in the problem
    IVar u = problem.createIntegerVariable();
    problem.require(SmtFactory.createConjunction(x, SmtFactory.createGreater(z, u)));
    a = solver.checkSatisfiability(problem);
    System.out.println(a);
    if (a instanceof Answer.MAYBE(String reason)) {
      System.out.println(reason);
    }
    else assertTrue(false);
    problem.clear();
  }
}
