/**************************************************************************************************
 Copyright 2024-2025 Cynthia Kop

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
import java.util.function.BiFunction;

import charlie.terms.FunctionSymbol;
import charlie.terms.Term;
import charlie.terms.TheoryFactory;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.smt.BVar;
import charlie.smt.SmtProblem;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.termination.reduction_pairs.OrderingRequirement.Relation;

public class ReductionPairProofObjectTest {
  private TRS makeTrs(String txt) {
    return CoraInputReader.readTrsFromString(txt);
  }

  private class MyClass extends ReductionPairProofObject {
    MyClass(OrderingProblem problem, Set<Integer> strictlyOriented, Set<Integer> cond,
            BiFunction<FunctionSymbol,Integer,Boolean> regards) {
      super(problem, strictlyOriented, cond, regards); 
    }
    public void justify(OutputModule module) {
      module.println("RPPO for the problem:");
      printOrderingProblem(module);
    }
  }

  private OrderingProblem createProblem(TRS trs) {
    Term l = TheoryFactory.createValue(9);
    Term r = TheoryFactory.createValue(7);
    Term q = TheoryFactory.createValue(42);
    Term c1 = TheoryFactory.createValue(false);
    Term c2 = TheoryFactory.createValue(true);
    SmtProblem smt = new SmtProblem();
    BVar a = smt.createBooleanVariable("A");
    BVar b = smt.createBooleanVariable("B");
    OrderingProblem prob = new OrderingProblem(trs, new ArgumentFilter(smt));
    for (Rule rho : trs.queryRules()) prob.require(new OrderingRequirement(rho, Relation.Weak));
    prob.requireEither(new OrderingRequirement(l,r,c1, Relation.Strict, List.of()), 12);
    prob.requireEither(new OrderingRequirement(l,r,c2, Relation.Weak, List.of()), -19);
    prob.requireConditionally(new OrderingRequirement(q,l,c1, Relation.Strict, Set.of()), a);
    prob.requireConditionally(new OrderingRequirement(r,q,c2, Relation.Weak, Set.of()), b);
    return prob;
  }

  @Test
  public void testStrictness() {
    TRS trs = makeTrs("sum :: Int -> Int sum(0) -> 0 sum(x) -> x + sum(x-1) | x != 0");
    OrderingProblem problem = createProblem(trs);
    ReductionPairProofObject rppo = new MyClass(problem, Set.of(12), Set.of(0), (f,i) -> true);
    assertTrue(rppo.queryAnswer() == ProofObject.Answer.YES);
    assertTrue(rppo.isStrictlyOriented(12));
    assertFalse(rppo.isStrictlyOriented(-19));
  }

  @Test
  public void testRegards() {
    TRS trs = makeTrs("sum :: Int -> Int f :: test -> test " +
                      "sum(0) -> 0 sum(x) -> x + sum(x-1) | x != 0");
    OrderingProblem problem = createProblem(trs);
    ReductionPairProofObject rppo = new MyClass(problem, Set.of(12), Set.of(0), (f,i) -> {
      if (f.queryName().equals("sum")) return i == 1;
      if (f.isTheorySymbol()) return i == 2;
      return false;
    });
    FunctionSymbol sum = trs.lookupSymbol("sum");
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    FunctionSymbol f = trs.lookupSymbol("f");
    assertTrue(rppo.regards(sum, 1));
    assertFalse(rppo.regards(sum, 2));
    assertFalse(rppo.regards(f, 1));
    assertFalse(rppo.regards(f, 2));
    assertFalse(rppo.regards(plus, 1));
    assertTrue(rppo.regards(plus, 2));
  }

  @Test
  public void testOutput() {
    TRS trs = makeTrs("sum :: Int -> Int sum(0) -> 0 sum(x) -> x + sum(x-1) | x != 0");
    ReductionPairProofObject rppo = new MyClass(createProblem(trs), Set.of(-19), Set.of(0),
      (f,k) -> false);
    OutputModule module = OutputModule.createUnicodeModule(trs);
    rppo.justify(module);
    assertTrue(module.toString().equals(
      "RPPO for the problem:\n\n" +
      "  9 ≽ 7 | false\n" +
      "  9 ≻ 7\n" +
      "  sum(0) ≽ 0\n" +
      "  sum(x) ≽ x + sum(x - 1) | x ≠ 0\n" +
      "  42 ≻ 9 | false\n\n"));
  }
}

