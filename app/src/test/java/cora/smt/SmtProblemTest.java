/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.smt;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.TreeSet;

public class SmtProblemTest {
  private SmtProblem exampleProblem() {
    // x > 1 ∨ x < 0
    // y = 3 ∧ (y != x ∨ z)
    // y = 9
    SmtProblem problem = new SmtProblem();
    IVar x = problem.createIntegerVariable();
    IVar y = problem.createIntegerVariable();
    BVar z = problem.createBooleanVariable();
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
      "(or (> i1 1) (> 0 i1))\n" +
      "(and (= i2 3) (or (distinct i2 i1) b1))\n" +
      "(= i2 9)\n"));
    assertTrue(problem.toString(1).equals(
      "(or (> i1 1) (> 0 i1))\n"));
    assertTrue(problem.toString(3).equals(problem.toString()));
    assertTrue(problem.toString(4).equals(problem.toString()));
    assertTrue(problem.toString(-2).equals(
      "(and (= i2 3) (or (distinct i2 i1) b1))\n" +
      "(= i2 9)\n"));
    assertTrue(problem.toString(-3).equals(problem.toString()));
    assertTrue(problem.toString(-4).equals(problem.toString()));
    assertTrue(problem.toString(0).equals(""));
  }

  @Test
  public void testCombinedConstraint() {
    SmtProblem problem = exampleProblem();
    assertTrue(problem.queryCombinedConstraint().toString().equals("(and " +
      "(or (> i1 1) (> 0 i1)) " +
      "(= i2 3) " +
      "(or (distinct i2 i1) b1) " +
      "(= i2 9))"));
  }

  @Test
  public void testCreateVariables() {
    SmtProblem problem = new SmtProblem();
    IVar a = problem.createIntegerVariable();
    IVar b = problem.createIntegerVariable();
    BVar c = problem.createBooleanVariable();
    IVar d = problem.createIntegerVariable();
    BVar e = problem.createBooleanVariable();
    assertTrue(a.queryIndex() == 1);
    assertTrue(b.queryIndex() == 2);
    assertTrue(c.queryIndex() == 1);
    assertTrue(d.queryIndex() == 3);
    assertTrue(e.queryIndex() == 2);
  }
}

