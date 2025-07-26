/**************************************************************************************************
 Copyright 2023--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.smt;

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
    Constraint conj =
      new Conjunction(new BVar(1), SmtFactory.createGreater(new IValue(2), new IVar(3)));
    Constraint conj2 =
      new Conjunction(new BVar(1), SmtFactory.createGreater(new IValue(2), new IVar(3)));
    Constraint conj3 =
      new Disjunction(new BVar(1), SmtFactory.createGreater(new IValue(2), new IVar(3)));
    Constraint conj4 =
      new Conjunction(SmtFactory.createGreater(new IValue(2), new IVar(3)), new BVar(1));
    assertTrue(conj.equals(conj2));
    assertFalse(conj.equals(conj3));
    assertFalse(conj.equals(conj4));
    assertTrue(conj.hashCode() == conj2.hashCode());
    assertTrue(conj.hashCode() != conj3.hashCode());
    assertTrue(conj.hashCode() != conj4.hashCode());
  }

  @Test
  public void testComparison() {
    Constraint conj =
      new Conjunction(new BVar(1), SmtFactory.createGreater(new IValue(2), new IVar(3)));
    Constraint conj2 =
      new Conjunction(new BVar(1), SmtFactory.createGreater(new IValue(2), new IVar(3)));
    Constraint conj3 =
      new Disjunction(new BVar(1), SmtFactory.createGreater(new IValue(2), new IVar(3)));
    Constraint conj4 =
      new Conjunction(SmtFactory.createGreater(new IValue(2), new IVar(3)), new BVar(1));
    Constraint conj5 = new Conjunction(new Truth(), new Conjunction(new Truth(), new Falsehood()));
    assertTrue(conj.compareTo(conj2) == 0);
    assertTrue(conj.compareTo(conj3) < 0);  // conjunction < disjunction
    assertTrue(conj.compareTo(conj4) < 0);  // same number of arguments, smaller first one
    assertTrue(conj4.compareTo(conj) > 0);
    assertTrue(conj.compareTo(conj5) < 0);  // fewer arguments
    assertTrue(conj5.compareTo(conj) > 0);  // fewer arguments
  }

  @Test
  public void testToString() {
    ArrayList<Constraint> args = new ArrayList<Constraint>();
    args.add(new Truth());
    args.add(SmtFactory.createGeq(new IValue(7), new IVar(12)));
    args.add(new BVar(12));
    Constraint conj = new Conjunction(args);
    assertTrue(conj.toSmtString().equals("(and true (>= (+ 7 (- i12)) 0) b12)"));
    assertTrue(conj.toString().equals("true and (7 >= i12) and b12"));
  }

  @Test
  public void testEvaluate() {
    Constraint conj = new Conjunction(SmtFactory.createGreater(new IValue(3), new IValue(-1000)),
      new Conjunction(new Truth(), SmtFactory.createGeq(new IValue(0), new IValue(0))));
    assertTrue(conj.evaluate());
    conj = new Conjunction(new Falsehood(), new BVar(7));
    assertFalse(conj.evaluate()); // this works despite the conjunction not being ground,
                                  // because and is evaluated left-to-right
  }

  @Test
  public void testQueryBadChild() {
    Conjunction conj = new Conjunction(new BVar(2), new Falsehood());
    assertThrows(java.lang.IndexOutOfBoundsException.class, () -> conj.queryChild(0));
    assertThrows(java.lang.IndexOutOfBoundsException.class, () -> conj.queryChild(3));
  }

  @Test
  public void testNegation() {
    Conjunction conj = new Conjunction(new Geq0(new IVar(3), new IValue(7)),
      new Conjunction(new BVar(2), new NBVar(new BVar(12))));
    assertTrue(conj.negate().negate().equals(conj));
    assertTrue(conj.negate().toString().equals("(6 >= i3) or !b2 or b12"));
  }

  @Test
  public void testNegationSimplifies() {
    IVar x = new IVar(2, "x");
    IntegerExpression three = new IValue(3);
    // x # 3 ∧ 3 > x
    Conjunction conj = new Conjunction((new Neq0(x, three)).simplify(),
                                       (new Geq0(three, x.add(1))).simplify());
    assertTrue(conj.isSimplified());
    // negation is x = 3 ∨ x ≥ 3, but that one can be easily simplified by dropping the first part
    assertTrue(conj.negate().toString().equals("[x] >= 3"));
  }

  @Test
  public void testSimplifyConstants() {
    IVar i = new IVar(1, "i");
    BVar x = new BVar(2, "x");

    // T ∧ x ∧ i >= 0 -- the only non-simplified aspect is the T
    Conjunction conj = new Conjunction(new Truth(), new Conjunction(x, new Geq0(i)));
    assertFalse(conj.isSimplified());
    assertTrue(conj.simplify().toString().equals("[x] and ([i] >= 0)"));

    // !x ∧ T -- so they're in the wrong order AND there's a T
    conj = new Conjunction(new NBVar(x), new Truth());
    assertFalse(conj.isSimplified());
    assertTrue(conj.simplify().equals(new NBVar(x)));

    // T ∧ T ∧ x -- so both T values need to be removed
    conj = new Conjunction(new Truth(), new Conjunction(new Truth(), x));
    assertTrue(conj.simplify() == x);

    // F ∧ x ∧ i >= 0 -- this is simplified to F
    conj = new Conjunction(new Falsehood(), new Conjunction(x, new Geq0(i)));
    assertTrue(conj.simplify().equals(new Falsehood()));

    // same for x ∧ F
    conj = new Conjunction(x, new Falsehood());
    assertTrue(conj.simplify().equals(new Falsehood()));
  }

  @Test
  public void testSimplifyArguments() {
    IVar x = new IVar(3, "x");
    BVar y = new BVar(1, "y");
    SVar z = new SVar(1, "z");
    IntegerExpression zero = new IValue(0);

    Conjunction conj = new Conjunction(y, new Geq0(new Addition(x, zero)));
    assertFalse(conj.isSimplified());
    assertTrue(conj.simplify().toString().equals("[y] and ([x] >= 0)"));

    conj = new Conjunction(new Geq0(new Addition(x, zero)), new EqS(z, new SValue("a")));
    assertFalse(conj.isSimplified());
    assertTrue(conj.simplify().toString().equals("([x] >= 0) and ([z] = \"a\")"));

    conj = new Conjunction(new Is0(new Addition(x, zero)), new Is0(x));
    assertTrue(conj.simplify().equals(new Is0(x)));
  }

  @Test
  public void testSimplifyComponentsAndReorder() {
    ArrayList<Constraint> parts = new ArrayList<Constraint>();
    parts.add(new Is0((new IVar(3, "i")).add(5)));
    parts.add(new NBVar(new BVar(3, "y")));
    parts.add(new Geq0((new IVar(3, "j")).add(4)));
    parts.add(new Neq0(new IValue(7)));
    parts.add(new EqS(new SVar(8, "s"), new SValue("test")));
    parts.add(new Neq0(new Multiplication(new IVar(1, "a"), new IVar(2, "b"))));
    parts.add(new Geq0(new Division(new CMult(3, new IVar(3, "i")), new IValue(-2))));
    parts.add(new BVar(12, "x"));
    parts.add(new Is0((new IVar(3, "i")).add(5)));
    parts.add(new UneqS(new SVar(7, "t"), new SValue("test")));
    Conjunction conj = new Conjunction(parts);
    assertTrue(conj.simplify().toString().equals(
      "![y] and [x] and ([a] # 0) and ([b] # 0) and (4 + [j] >= 0) and (5 + [i] = 0) " +
      "and (-((3 * [i]) / 2) >= 0) and ([t] # \"test\") and ([s] = \"test\")"));
  }

  @Test
  public void testSimplifyCombine() {
    BVar x = new BVar(3, "x");
    IVar y = new IVar(1, "y");
    SVar z = new SVar(2, "z");
    SVar a = new SVar(3, "a");
    Conjunction conj = new Conjunction(x, x.negate());
    assertTrue(conj.simplify().equals(new Falsehood()));

    IntegerExpression expr = y.add(-1);
    conj = new Conjunction(new Neq0(expr), new Is0(expr));
    assertTrue(conj.simplify().equals(new Falsehood()));

    StringExpression v = new SValue("A");
    conj = new Conjunction(new EqS(z, v), new Conjunction(new EqS(a, v), new UneqS(z, v)));
    assertTrue(conj.simplify().equals(new Falsehood()));
  }

  @Test
  public void testSimplifyWithComparison() {
    IVar x = new IVar(1, "x");
    Conjunction conj = new Conjunction(new Is0(x), new Geq0(x));
    assertTrue(conj.simplify().toString().equals("[x] = 0"));

    conj = new Conjunction(new Neq0(x), new Geq0(x));
    assertTrue(conj.simplify().toString().equals("[x] >= 1"));
  }
}
