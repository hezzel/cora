/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions or limitations under the License.
 *************************************************************************************************/

package charlie.smt;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;

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
    Constraint disj =
      new Disjunction(new BVar(1), SmtFactory.createGreater(new IValue(2), new IVar(3)));
    Constraint disj2 =
      new Disjunction(new BVar(1),SmtFactory.createGreater(new IValue(2), new IVar(3)));
    Constraint conj = new Conjunction(new BVar(1),
      SmtFactory.createGreater(new IValue(2), new IVar(3)));
    assertTrue(disj.equals(disj2));
    assertTrue(disj.hashCode() == disj2.hashCode());
    assertTrue(disj.hashCode() != conj.hashCode());
    assertFalse(disj.equals(conj));
    assertFalse(disj.equals(new Disjunction(
      SmtFactory.createGreater(new IValue(2), new IVar(3)), new BVar(1))));
  }

  @Test
  public void testComparison() {
    Constraint disj = new Disjunction(new BVar(2), new BVar(3));
    Constraint disj2 = new Disjunction(List.of(new BVar(12)));
    Constraint disj3 = new Disjunction(List.of(new BVar(1), new BVar(7), new BVar(2)));
    Constraint disj4 = new Disjunction(new BVar(3), new BVar(2));
    Constraint conj = new Conjunction(new BVar(2), new BVar(3));
    assertTrue(disj.compareTo(disj2) > 0);  // more arguments
    assertTrue(disj.compareTo(disj3) < 0);  // fewer arguments
    assertTrue(disj.compareTo(disj4) < 0);  // first argument is smaller
    assertTrue(disj.compareTo(conj) > 0);   // conjunctions before disjunctions
  }

  @Test
  public void testToString() {
    List<Constraint> args = List.of(new Truth(),
                                    SmtFactory.createGeq(new IValue(7), new IVar(12)),
                                    new BVar(12, "x"));
    Constraint disj = new Disjunction(args);
    assertTrue(disj.toSmtString().equals("(or true (>= (+ 7 (- i12)) 0) b12)"));
    assertTrue(disj.toString().equals("true or (7 >= i12) or [x]"));
  }

  @Test
  public void testEvaluate() {
    Constraint disj = new Disjunction(SmtFactory.createGreater(new IValue(3), new IValue(12)),
      new Disjunction(new Falsehood(), SmtFactory.createGeq(new IValue(0), new IValue(0))));
    assertTrue(disj.evaluate());
    disj = new Disjunction(SmtFactory.createGreater(new IValue(3), new IValue(12)),
      new Disjunction(new Falsehood(), SmtFactory.createGeq(new IValue(0), new IValue(1))));
    assertFalse(disj.evaluate());
    disj = new Disjunction(new Truth(), new BVar(7));
    assertTrue(disj.evaluate());
  }


  @Test
  public void testNegation() {
    Disjunction disj = new Disjunction(new Geq0(new IVar(3), new IValue(7)),
      new Conjunction(new BVar(2), new NBVar(new BVar(12))));
    assertTrue(disj.negate().negate().equals(disj));
    assertTrue(disj.negate().toString().equals("(6 >= i3) and (!b2 or b12)"));
  }
}
