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

package cora.termination.reduction_pairs;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;

import charlie.terms.Term;
import charlie.terms.TheoryFactory;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;

public class OrderingRequirementTest {
  private TRS makeTrs(String txt) {
    return CoraInputReader.readTrsFromString(txt);
  }

  @Test
  public void testPrintVariablesCorrectly() {
    // we test this via OrderingProblem, since it's the most convenient way to access an
    // OutputModule print
    TRS trs = makeTrs("f :: Int -> Int g :: Int -> Int -> Int f(x) -> g(x,y) | x > 0");
    OrderingProblem problem = OrderingProblem.createStrictProblem(trs);
    assertTrue(problem.toString().equals("  f(x) ≻ g(x, y) | x > 0 { x y }\n\n"));
    trs = makeTrs("f :: Int -> Int g :: Int -> Int -> Int f(x) -> g(x,0) | x > 0");
    problem = OrderingProblem.createWeakProblem(trs, List.of());
    assertTrue(problem.toString().equals("  f(x) ≽ g(x, 0) | x > 0\n\n"));
  }
}

