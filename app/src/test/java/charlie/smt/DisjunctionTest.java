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

  @Test
  public void testNegationSimplifies() {
    IVar x = new IVar(2, "x");
    IntegerExpression three = new IValue(3);
    // 3 # x ∨ 3 > x
    Disjunction disj = new Disjunction((new Neq0(x, three)).simplify(),
                                       (new Geq0(three, x.add(1))).simplify());
    assertTrue(disj.isSimplified());
    // negation is x = 3 ∧ x ≥ 3, but that one can be easily simplified by dropping the second part
    assertTrue(disj.negate().toString().equals("[x] = 3"));
  }

  @Test
  public void testSimplifyConstants() {
    IVar i = new IVar(1, "i");
    BVar x = new BVar(2, "x");

    // F ∨ x ∨ i >= 0 -- the only non-simplified aspect is the F
    Disjunction disj = new Disjunction(new Falsehood(), new Disjunction(x, new Geq0(i)));
    assertFalse(disj.isSimplified());
    assertTrue(disj.simplify().toString().equals("[x] or ([i] >= 0)"));

    // !x ∨ F -- so they're in the wrong order AND there's a F
    disj = new Disjunction(new NBVar(x), new Falsehood());
    assertFalse(disj.isSimplified());
    assertTrue(disj.simplify().equals(new NBVar(x)));

    // F ∨ F ∨ x -- so both F values need to be removed
    disj = new Disjunction(new Falsehood(), new Disjunction(new Falsehood(), x));
    assertTrue(disj.simplify() == x);

    // T ∨ x ∨ i >= 0 -- this is simplified to T
    disj = new Disjunction(new Truth(), new Disjunction(x, new Geq0(i)));
    assertTrue(disj.simplify().equals(new Truth()));

    // same for x ∨ (i = i)
    disj = new Disjunction(x, new Is0(i, i));
    assertTrue(disj.simplify().equals(new Truth()));
  }

  @Test
  public void testSimplifyArguments() {
    IVar x = new IVar(3, "x");
    BVar y = new BVar(1, "y");
    SVar z = new SVar(1, "z");
    IntegerExpression zero = new IValue(0);

    Disjunction disj = new Disjunction(y, new Geq0(new Addition(x, zero)));
    assertFalse(disj.isSimplified());
    assertTrue(disj.simplify().toString().equals("[y] or ([x] >= 0)"));

    disj = new Disjunction(new Geq0(new Addition(x, zero)), new EqS(z, new SValue("a")));
    assertFalse(disj.isSimplified());
    assertTrue(disj.simplify().toString().equals("([x] >= 0) or ([z] = \"a\")"));

    disj = new Disjunction(new Is0(new Addition(x, zero)), new Is0(x));
    assertTrue(disj.simplify().equals(new Is0(x)));
  }

  @Test
  public void testSimplifyComponentsAndReorder() {
    ArrayList<Constraint> parts = new ArrayList<Constraint>();
    // i + 5 = 0
    parts.add(new Is0((new IVar(3, "i")).add(5)));
    // !y
    parts.add(new NBVar(new BVar(3, "y")));
    // j + 4 >= 0
    parts.add(new Geq0((new IVar(3, "j")).add(4)));
    // 7 = 0
    parts.add(new Is0(new IValue(7)));
    // s = "test"
    parts.add(new EqS(new SVar(8, "s"), new SValue("test")));
    // a * b = 0
    parts.add(new Is0(new Multiplication(new IVar(1, "a"), new IVar(2, "b"))));
    // (3 * i) / -2 >= 0
    parts.add(new Geq0(new Division(new CMult(3, new IVar(3, "i")), new IValue(-2))));
    // x
    parts.add(new BVar(12, "x"));
    // i + 5 = 0
    parts.add(new Is0((new IVar(3, "i")).add(5)));
    // t != "test"
    parts.add(new UneqS(new SVar(7, "t"), new SValue("test")));
    Disjunction disj = new Disjunction(parts);
    assertTrue(disj.simplify().toString().equals(
      "![y] or [x] or ([a] = 0) or ([b] = 0) or (4 + [j] >= 0) or (5 + [i] = 0) " +
      "or (-((3 * [i]) / 2) >= 0) or ([t] # \"test\") or ([s] = \"test\")"));
  }

  @Test
  public void testSimplifyCombine() {
    BVar x = new BVar(3, "x");
    IVar y = new IVar(1, "y");
    SVar z = new SVar(2, "z");
    SVar a = new SVar(3, "a");

    // x ∨ !x
    Disjunction disj = new Disjunction(x, x.negate());
    assertTrue(disj.simplify().equals(new Truth()));

    // y + 1 # 0 ∨ y + 1 = 0
    IntegerExpression expr = y.add(-1);
    disj = new Disjunction(new Neq0(expr), new Is0(expr));
    assertTrue(disj.simplify().equals(new Truth()));

    // z = "A" ∨ a = "A" ∨ z # "A"
    StringExpression v = new SValue("A");
    disj = new Disjunction(new EqS(z, v), new Disjunction(new EqS(a, v), new UneqS(z, v)));
    assertTrue(disj.simplify().equals(new Truth()));
  }

  @Test
  public void testSimplifyWithComparison() {
    IVar x = new IVar(1, "x");

    // x = 0 ∨ x ≥ 0
    Disjunction disj = new Disjunction(new Is0(x), new Geq0(x));
    assertTrue(disj.simplify().toString().equals("[x] >= 0"));

    // x # 0 ∨ x ≥ 0
    disj = new Disjunction(new Neq0(x), new Geq0(x));
    assertTrue(disj.simplify().equals(new Truth()));
  }
}

