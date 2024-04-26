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
import java.util.Set;
import java.util.TreeMap;
import charlie.terms.Term;
import charlie.terms.TheoryFactory;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.termination.TerminationAnswer;

public class ReductionPairProofObjectTest {
  private TRS makeTrs(String txt) {
    return CoraInputReader.readTrsFromString(txt);
  }

  private class MyClass extends ReductionPairProofObject {
    MyClass(OrderingProblem problem, Set<Integer> strictlyOriented) {
      super(problem, strictlyOriented); 
    }
    public void justify(OutputModule module) {
      module.println("RPPO for the problem:");
      printOrderingProblem(module);
    }
  }

  private OrderingProblem createProblem() {
    TRS trs = makeTrs("sum :: Int -> Int sum(0) -> 0 sum(x) -> x + sum(x-1) | x != 0");
    Term l = TheoryFactory.createValue(9);
    Term r = TheoryFactory.createValue(7);
    Term c1 = TheoryFactory.createValue(false);
    Term c2 = TheoryFactory.createValue(true);
    OrderingRequirement req1 =
      new OrderingRequirement(l,r,c1, OrderingRequirement.Relation.Either, List.of());
    OrderingRequirement req2 =
      new OrderingRequirement(l,r,c2, OrderingRequirement.Relation.Strict, List.of());
    return OrderingProblem.createWeakProblem(trs, List.of(req1, req2));
  }

  @Test
  public void testStrictness() {
    OrderingProblem problem = createProblem();
    ReductionPairProofObject rppo = new MyClass(problem, Set.of(1));
    assertTrue(rppo.queryAnswer() == TerminationAnswer.YES);
    assertFalse(rppo.isStrictlyOriented(0));
    assertFalse(rppo.isStrictlyOriented(problem.reqs().get(0)));
    assertTrue(rppo.isStrictlyOriented(1));
    assertTrue(rppo.isStrictlyOriented(problem.reqs().get(1)));
  }

  @Test
  public void testOutput() {
    ReductionPairProofObject rppo = new MyClass(createProblem(), Set.of(1));
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    rppo.justify(module);
    assertTrue(module.toString().equals(
      "RPPO for the problem:\n\n" +
      "  9 ≽ 7 | false\n" +
      "  9 ≻ 7\n" +
      "  sum(0) ≽ 0\n" +
      "  sum(x) ≽ x + sum(x - 1) | x ≠ 0\n\n"));
  }
}

