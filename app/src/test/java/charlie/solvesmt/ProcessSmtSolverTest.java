package charlie.solvesmt;

import charlie.smt.*;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class ProcessSmtSolverTest {

  @Test
  void checkSatisfiability() {
  }

  @Test
  void checkValidity() {
  }

  @Test
  public void testSimpleValidityCheck() {
    ProcessSmtSolver solver = new ProcessSmtSolver();
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
    problem.require(SmtFactory.createConjunction(x, SmtFactory.createConjunction(le, SmtFactory.createConjunction(gr, eq))));
    assertTrue(solver.checkSatisfiability(problem) instanceof SmtSolver.Answer.NO);
    problem.clear();

    // x ∧ z < 10 ∧ (y > 12 ∨ y = z)
    problem.require(SmtFactory.createConjunction(x, SmtFactory.createConjunction(le, SmtFactory.createDisjunction(gr, eq))));
    SmtSolver.Answer a = solver.checkSatisfiability(problem);
    if (a instanceof SmtSolver.Answer.YES(Valuation v)) {
      assertTrue(v.queryAssignment(x));
      assertTrue(v.queryAssignment(z) < 0);
      assertTrue(v.queryAssignment(y) > 12 || v.queryAssignment(y) == v.queryAssignment(z));
      System.out.println(v);
    }
    else assertTrue(false);
    problem.clear();
  }

}
