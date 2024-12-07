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

package cora.rwinduction.engine;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.Set;

import charlie.terms.Term;
import charlie.terms.Renaming;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;

class EquationTest {
  @Test
  public void testToString() {
    Renaming renaming = new Renaming(Set.of());
    TRS trs = CoraInputReader.readTrsFromString(
      "sum1 :: Int -> Int\n" +
      "sum2 :: Int -> Int\n");
    Term left = CoraInputReader.readTerm("sum1(x)", renaming, true, trs);
    Term right = CoraInputReader.readTerm("sum2(x + y)", renaming, true, trs);
    Term constraint = CoraInputReader.readTerm("x > 0 ∧ y = 0", renaming, true, trs);
    Equation equation = new Equation(left, right, constraint, renaming);
    assertTrue(equation.toString().equals("sum1(x) ≈ sum2(x + y) | x > 0 ∧ y = 0"));
  }
}

