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

public class SmtSolverTest {
  // @Test
  // NOTE: @Test removed because we don't want to be writing files at every compile
  public void testSimpleValidityCheck() {
    SmtSolver solver = new SmtSolver();

    TreeSet<Integer> boolvars = new TreeSet<Integer>();
    TreeSet<Integer> intvars = new TreeSet<Integer>();
    intvars.add(1);

    // x > 1 => x > 0 is valid
    IVar x = new IVar(1);
    Constraint gr1 = new Greater(x, new IValue(1));
    Constraint gr0 = new Greater(x, new IValue(0));
    Constraint c = new Disjunction(new Not(gr1), gr0);
    assertTrue(solver.checkValidity(boolvars, intvars, c));
    // x > 0 => x > 1 is not valid
    c = new Disjunction(new Not(gr0), gr1);
    assertFalse(solver.checkValidity(boolvars, intvars, c));
  }

  // @Test
  // NOTE: @Test removed because we don't want to be writing files at every compile
  public void testSimpleSatisfiabilityCheck() {
    SmtSolver solver = new SmtSolver();

    TreeSet<Integer> boolvars = new TreeSet<Integer>();
    TreeSet<Integer> intvars = new TreeSet<Integer>();
    boolvars.add(1);
    intvars.add(2);
    intvars.add(3);
    intvars.add(4);
    boolvars.add(5);

    // x ∧ z < 0 ∧ y > 12 ∧ y = z
    BVar x = new BVar(1);
    IVar y = new IVar(2);
    IVar z = new IVar(3);
    Constraint le = new Greater(new IValue(0), z);
    Constraint gr = new Greater(y, new IValue(12));
    Constraint eq = new Equal(y, z);
    Constraint c = new Conjunction(x, new Conjunction(le, new Conjunction(gr, eq)));
    assertTrue(solver.checkSatisfiability(boolvars, intvars, c) == null);
    // x ∧ z < 10 ∧ (y > 12 ∨ y = z)
    c = new Conjunction(x, new Conjunction(le, new Disjunction(gr, eq)));
    Valuation v = solver.checkSatisfiability(boolvars, intvars, c);
    assertTrue(v != null);
    assertTrue(v.queryAssignment(x));
    assertTrue(v.queryAssignment(z) < 0);
    assertTrue(v.queryAssignment(y) > 12 || v.queryAssignment(y) == v.queryAssignment(z));
    System.out.println(v);
  }
}

