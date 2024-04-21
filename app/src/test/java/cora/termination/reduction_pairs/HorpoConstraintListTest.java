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
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import charlie.types.Type;
import charlie.terms.position.Position;
import charlie.terms.*;
import charlie.smt.BVar;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;

public class HorpoConstraintListTest {
  private TRS makeTrs(String txt) {
    return CoraInputReader.readTrsFromString(txt);
  }

  private Type type(String txt) {
    return CoraInputReader.readType(txt);
  }

  private HorpoConstraintList makeList(HorpoParameters param, TRS trs) {
    return new HorpoConstraintList(param, new TermPrinter(trs.queryAlphabet().getSymbols().stream()
                                      .map(FunctionSymbol::queryName).collect(Collectors.toSet())));
  }

  @Test
  public void testStoreDifferentThings() {
    TRS trs = makeTrs("f :: Int -> Int -> Int g :: Int -> Int -> Int d :: Int -> Int");
    HorpoConstraintList lst = makeList(new HorpoParameters(1000, true), trs);
    Rule rule = CoraInputReader.readRule("f(x, d(y)) -> g(x,x) | x > 0", trs);
    BVar x1 = lst.store(rule.queryLeftSide(), lst.GREATER, rule.queryRightSide(),
                        rule.queryConstraint());
    rule = CoraInputReader.readRule("g(x, d(x)) -> f(y,x)", trs);
    Term right = rule.queryRightSide();
    TreeSet<Variable> vars = new TreeSet<Variable>(
      Set.of(right.querySubterm(Position.parse("1")).queryVariable(),
      TermFactory.createVar("z", type("Int")))
    );
    BVar x2 = lst.getVariableFor(rule.queryLeftSide(), lst.GEQ, right, rule.queryConstraint(),
                                 vars, "myclause");
    assertTrue(x1 != x2);
    assertTrue(lst.toString().equals(
      "@ [f(x, d(y)) ≻ g(x, x) | x > 0 { x }]\n" +
      "@ [g(x, d(x)) ≽ f(y, x) | true { y } by myclause]\n"));
  }

  @Test
  public void testStoreTheSameThing() {
    TRS trs = makeTrs("f :: Int -> Int -> Int g :: Int -> Int -> Int d :: Int -> Int");
    HorpoConstraintList lst = makeList(new HorpoParameters(1000, false), trs);
    Rule rule = CoraInputReader.readRule("f(x, d(y)) -> g(x,x) | x > 0", trs);
    BVar x1 = lst.store(rule.queryLeftSide(), lst.GREATER, rule.queryRightSide(),
                        rule.queryConstraint());
    rule = CoraInputReader.readRule("f(x, d(y)) -> g(x,x) | x > 0", trs);
    TreeSet<Variable> vars = new TreeSet<Variable>();
    for (Variable x : rule.queryRightSide().vars()) vars.add(x);
    vars.add(TermFactory.createVar("z", type("Int")));
    BVar x2 = lst.getVariableFor(rule.queryLeftSide(), lst.GREATER, rule.queryRightSide(),
                                 rule.queryConstraint(), vars, null);
    assertTrue(x1 == x2);
    assertTrue(lst.toString().equals("@ [f(x, d(y)) ≻ g(x, x) | x > 0 { x }]\n"));
  }
}

