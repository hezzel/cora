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

public class SmtProblemTest {
  private SmtProblem exampleProblem() {
    // x > 1 ∨ x < 0
    // y = 3 ∧ (y != x ∨ z)
    // y = 9
    SmtProblem problem = new SmtProblem();
    IVar x = problem.createIntegerVariable("x");
    IVar y = problem.createIntegerVariable("y");
    BVar z = problem.createBooleanVariable("z");
    problem.require(SmtFactory.createDisjunction(SmtFactory.createGreater(x,
      SmtFactory.createValue(1)), SmtFactory.createSmaller(x, SmtFactory.createValue(0))));
    problem.require(SmtFactory.createConjunction(SmtFactory.createEqual(y,
      SmtFactory.createValue(3)), SmtFactory.createDisjunction(SmtFactory.createUnequal(y, x), z)));
    problem.require(SmtFactory.createEqual(y, SmtFactory.createValue(9)));
    return problem;
  }

  @Test
  public void testToString() {
    SmtProblem problem = exampleProblem();
    assertTrue(problem.toString().equals(
      "([x] >= 2) or (0 >= 1 + [x])\n" +
      "([y] = 3) and (([y] # [x]) or [z])\n" +
      "[y] = 9\n"));
    assertTrue(problem.toString(1).equals(
      "([x] >= 2) or (0 >= 1 + [x])\n"));
    assertTrue(problem.toString(3).equals(problem.toString()));
    assertTrue(problem.toString(4).equals(problem.toString()));
    assertTrue(problem.toString(-2).equals(
      "([y] = 3) and (([y] # [x]) or [z])\n" +
      "[y] = 9\n"));
    assertTrue(problem.toString(-3).equals(problem.toString()));
    assertTrue(problem.toString(-4).equals(problem.toString()));
    assertTrue(problem.toString(0).equals(""));
  }

  @Test
  public void testCombinedConstraint() {
    SmtProblem problem = exampleProblem();
    assertTrue(problem.queryCombinedConstraint().toString().equals(
      "(([x] >= 2) or (0 >= 1 + [x])) and " +
      "([y] = 3) and " +
      "(([y] # [x]) or [z]) and " +
      "([y] = 9)"));
  }

  @Test
  public void testCreateVariables() {
    SmtProblem problem = new SmtProblem();
    IVar a = problem.createIntegerVariable();
    IVar b = problem.createIntegerVariable("x");
    BVar c = problem.createBooleanVariable();
    IVar d = problem.createIntegerVariable("x");
    BVar e = problem.createBooleanVariable("y");
    assertTrue(a.queryIndex() == 1);
    assertTrue(b.queryIndex() == 2);
    assertTrue(c.queryIndex() == 1);
    assertTrue(d.queryIndex() == 3);
    assertTrue(e.queryIndex() == 2);
    assertTrue(a.queryName().equals("i1"));
    assertTrue(b.queryName().equals("[x]"));
    assertTrue(c.queryName().equals("b1"));
    assertTrue(d.queryName().equals("[x]"));
    assertTrue(e.queryName().equals("[y]"));
  }
}

