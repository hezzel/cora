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
import java.util.ArrayList;

public class ConjunctionTest {
  @Test
  public void testStaggeredCreation() {
    Conjunction conj = new Conjunction(new Truth(), new Conjunction(new BVar(12), new Falsehood()));
    assertTrue(conj.numChildren() == 3);
    assertTrue(conj.queryChild(1).equals(new Truth()));
    assertTrue(conj.queryChild(2).equals(new BVar(12)));
    assertTrue(conj.queryChild(3).equals(new Falsehood()));
  }

  @Test
  public void testEquality() {
    Constraint conj = new Conjunction(new BVar(1), new Greater(new IValue(2), new IVar(3)));
    assertTrue(conj.equals(new Conjunction(new BVar(1), new Greater(new IValue(2), new IVar(3)))));
    assertFalse(conj.equals(new Disjunction(new BVar(1), new Greater(new IValue(2), new IVar(3)))));
    assertFalse(conj.equals(new Conjunction(new Greater(new IValue(2), new IVar(3)), new BVar(1))));
  }

  @Test
  public void testToString() {
    ArrayList<Constraint> args = new ArrayList<Constraint>();
    args.add(new Truth());
    args.add(new Geq(new IValue(7), new IVar(12)));
    args.add(new BVar(12));
    Constraint conj = new Conjunction(args);
    assertTrue(conj.toString().equals("(and true (>= 7 i12) b12)"));
  }

  @Test
  public void testEvaluate() {
    Constraint conj = new Conjunction(new Greater(new IValue(3), new IValue(-1000)),
      new Conjunction(new Truth(), new Geq(new IValue(0), new IValue(0))));
    assertTrue(conj.evaluate());
    conj = new Conjunction(new Falsehood(), new BVar(7));
    assertFalse(conj.evaluate()); // this works despite the conjunction not being ground,
                                  // because and is evaluated left-to-right
  }

  @Test
  public void testQueryBadChild() {
    Conjunction conj = new Conjunction(new BVar(2), new Falsehood());
    assertThrows(charlie.exceptions.IndexingError.class, () -> conj.queryChild(0));
    assertThrows(charlie.exceptions.IndexingError.class, () -> conj.queryChild(3));
  }
}
