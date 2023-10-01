/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions or limitations under the License.
 *************************************************************************************************/

package cora.smt;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;

public class DisjunctionTest {
  @Test
  public void testStaggeredCreation() {
    Disjunction disj =
      new Disjunction(new Disjunction(new BVar(1), new Falsehood()), new Truth());
    assertTrue(disj.numChildren() == 3);
    assertTrue(disj.queryChild(1).equals(new BVar(1)));
    assertTrue(disj.queryChild(2).equals(new Falsehood()));
    assertTrue(disj.queryChild(3).equals(new Truth()));
  }

  @Test
  public void testEquality() {
    Constraint disj = new Disjunction(new BVar(1), new Greater(new IValue(2), new IVar(3)));
    assertTrue(disj.equals(new Disjunction(new BVar(1), new Greater(new IValue(2), new IVar(3)))));
    assertFalse(disj.equals(new Conjunction(new BVar(1), new Greater(new IValue(2), new IVar(3)))));
    assertFalse(
      disj.equals(new Disjunction(new Greater(new IValue(2), new IVar(3)), new BVar(1))));
  }

  @Test
  public void testToString() {
    ArrayList<Constraint> args = new ArrayList<Constraint>();
    args.add(new Truth());
    args.add(new Geq(new IValue(7), new IVar(12)));
    args.add(new BVar(12));
    Constraint disj = new Disjunction(args);
    assertTrue(disj.toString().equals("(or true (>= 7 i12) b12)"));
  }

  @Test
  public void testEvaluate() {
    Constraint disj = new Disjunction(new Greater(new IValue(3), new IValue(12)),
      new Disjunction(new Falsehood(), new Geq(new IValue(0), new IValue(0))));
    assertTrue(disj.evaluate());
    disj = new Disjunction(new Greater(new IValue(3), new IValue(12)),
      new Disjunction(new Falsehood(), new Geq(new IValue(0), new IValue(1))));
    assertFalse(disj.evaluate());
    disj = new Disjunction(new Truth(), new BVar(7));
    assertTrue(disj.evaluate());
  }
}
