/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.termination.dependency_pairs;

import charlie.types.TypeFactory;
import charlie.terms.Renaming;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.TheoryFactory;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;

import java.util.Set;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class DPTest {
  private TRS trs = CoraInputReader.readTrsFromString(
    "eval :: Int -> Int -> Int\n" +
    "eval(x, y) -> eval(x - 1, y) | x>y");

  @Test
  void testCreateFullDP() {
    Renaming renaming = new Renaming(Set.of());
    Term lhs = CoraInputReader.readTerm("eval(x, y)", renaming, true, trs);
    Term rhs = CoraInputReader.readTerm("eval(x-1, y)", renaming, true, trs);
    Term constraint = CoraInputReader.readTerm("x > y", renaming, true, trs);
    Set<Variable> vars = Set.of(renaming.getVariable("x"), renaming.getVariable("y"));
    DP dp = new DP(lhs, rhs, constraint, vars);
    assertTrue(dp.toString().equals("eval(x, y) => eval(x - 1, y) | x > y { }"));
  }

  @Test
  void testCreateFullDPWithExtraVariable() {
    Renaming renaming = new Renaming(Set.of());
    Term lhs = CoraInputReader.readTerm("eval(x, y)", renaming, true, trs);
    Term rhs = CoraInputReader.readTerm("eval(x-1, y)", renaming, true, trs);
    Term constraint = CoraInputReader.readTerm("x > y", renaming, true, trs);
    Set<Variable> vars = Set.of(renaming.getVariable("x"), renaming.getVariable("y"),
                                TheoryFactory.createVar("z", TypeFactory.boolSort));
    DP dp = new DP(lhs, rhs, constraint, vars);
    assertTrue(dp.toString().equals("eval(x, y) => eval(x - 1, y) | x > y { z }"));
  }

  @Test
  void testDeduceVariables() {
    Renaming renaming = new Renaming(Set.of());
    Term lhs = CoraInputReader.readTerm("eval(x, y)", renaming, true, trs);
    Term rhs = CoraInputReader.readTerm("eval(x-1, y)", renaming, true, trs);
    Term constraint = CoraInputReader.readTerm("x > y", renaming, true, trs);
    DP dp = new DP(lhs, rhs, constraint);
    assertTrue(dp.toString().equals("eval(x, y) => eval(x - 1, y) | x > y { }"));
  }

  @Test
  void testDeduceConstraint() {
    Renaming renaming = new Renaming(Set.of());
    Term lhs = CoraInputReader.readTerm("eval(x, x)", renaming, true, trs);
    Term rhs = CoraInputReader.readTerm("eval(x-1, y)", renaming, true, trs);
    DP dp = new DP(lhs, rhs);
    assertTrue(dp.toString().equals("eval(x, x) => eval(x - 1, y) | true { }"));
  }
}
