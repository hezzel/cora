/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

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
import java.util.List;

public class IffTest {
  @Test
  public void testToString() {
    IntegerExpression left = new IVar(7);
    IntegerExpression right = new Addition(new IValue(3), new IVar(1));
    Constraint comp = SmtFactory.createGreater(left, right);
    Constraint bvar = new BVar(9);
    Constraint iff = SmtFactory.createIff(comp, bvar);
    assertTrue(iff.toSmtString().equals("(= (>= (+ i7 (- 1) (- 3) (- i1)) 0) b9)"));
    assertTrue(iff.toString().equals("(i7 >= 4 + i1) == b9"));
  }

  @Test
  public void testEquality() {
    Constraint comp = SmtFactory.createSmaller(new IVar(2), new IValue(2));
    Constraint neg = SmtFactory.createNegation(comp);
    Constraint other = SmtFactory.createGeq(new IValue(3), new IVar(3));
    Constraint iff = SmtFactory.createIff(neg, other);
    assertTrue(iff.equals(iff));
    assertTrue(iff.equals(SmtFactory.createIff(neg, other)));
    assertFalse(iff.equals(SmtFactory.createIff(other, neg)));
    assertFalse(iff.equals(SmtFactory.createIff(neg, neg)));
    assertFalse(iff.equals(SmtFactory.createIff(other, other)));
    assertTrue(iff.hashCode() == SmtFactory.createIff(neg, other).hashCode());
    assertTrue(iff.hashCode() != SmtFactory.createIff(other, neg).hashCode());
  }

  @Test
  public void testCompareTo() {
    Constraint iff = new Iff(new BVar(12), new BVar(17));
    assertTrue(iff.compareTo(new Iff(new BVar(12), new BVar(17))) == 0);
    assertTrue(iff.compareTo(new Iff(new BVar(17), new BVar(1))) < 0);
    assertTrue(iff.compareTo(new Iff(new BVar(11), new BVar(17))) > 0);
  }

  @Test
  public void testLegalEvaluate() {
    Constraint a = SmtFactory.createNegation(new Truth());
    Constraint b = new Falsehood();
    Constraint iff1 = new Iff(a, b);
    Constraint iff2 = new Iff(SmtFactory.createNegation(b), a);
    assertTrue(iff1.evaluate());
    assertFalse(iff2.evaluate());
  }

  @Test
  public void testQueryParts() {
    Constraint comparison = SmtFactory.createSmaller(new IVar(1), new IValue(3));
    BVar a = new BVar(7);
    Iff i = new Iff(a, comparison);
    assertTrue(i.queryLeft().equals(a));
    assertTrue(i.queryRight().equals(comparison));
  }

  @Test
  public void testNegate() {
    IntegerExpression complex =
      new Addition(List.of(new IValue(3), new IVar(1), new CMult(-2, new IVar(7))));
    Constraint b7 = new BVar(7);
    Constraint b9 = new BVar(9);
    Constraint nb7 = new NBVar(new BVar(7));
    Constraint nb9 = new NBVar(new BVar(9));
    Constraint comp = new Is0(complex);
    Constraint ncomp = new Neq0(complex);
    Constraint iff = new Iff(nb7, b9);
    Constraint conj = new Conjunction(b7, comp);

    Iff a;

    a = new Iff(b9, b7);
    assertTrue(a.negate().equals(new Iff(nb9, b7)));
    a = new Iff(nb7, b9);
    assertTrue(a.negate().equals(new Iff(b7, b9)));
    a = new Iff(nb7, conj);
    assertTrue(a.negate().equals(new Iff(b7, conj)));
    a = new Iff(conj, b9);
    assertTrue(a.negate().equals(new Iff(conj, nb9)));
    a = new Iff(comp, nb7);
    assertTrue(a.negate().equals(new Iff(comp, b7)));
    a = new Iff(comp, conj);
    assertTrue(a.negate().equals(new Iff(ncomp, conj)));
    a = new Iff(conj, comp);
    assertTrue(a.negate().equals(new Iff(conj, ncomp)));
    a = new Iff(conj, iff);
    assertTrue(a.negate().equals(new Iff(conj, new Iff(b7, b9))));
    a = new Iff(comp, iff);
    assertTrue(a.negate().equals(new Iff(comp, new Iff(b7, b9))));
    a = new Iff(conj, conj);
    assertTrue(a.negate().equals(new Iff(new Disjunction(nb7, ncomp), conj)));
    assertTrue(a.negate().negate().equals(a));
  }

  @Test
  public void testSimplifyBasic() {
    BVar x = new BVar(3);
    BVar x4 = new BVar(4);
    NBVar y12 = new NBVar(new BVar(12));

    // x <--> !y
    Iff iff = new Iff(x, y12);
    assertTrue(iff.isSimplified());
    assertTrue(iff.simplify() == iff);

    // x <--> x
    iff = new Iff(x, new BVar(3));
    assertFalse(iff.isSimplified());
    assertTrue(iff.simplify().equals(new Truth()));

    // x4 <--> x -- so they need to be switched
    iff = new Iff(x4, x);
    assertFalse(iff.isSimplified());
    assertTrue(iff.simplify().equals(new Iff(x, x4)));
    assertTrue(iff.simplify().isSimplified());
  }

  @Test
  public void testSimplifyConstants() {
    BVar x = new BVar(3);
    BVar y = new BVar(4);

    // x <--> true -- this is just x
    Iff iff = new Iff(x, new Truth());
    assertFalse(iff.isSimplified());
    assertTrue(iff.simplify() == x);

    // x <--> false -- this is the negation of x
    iff = new Iff(x, new Falsehood());
    assertFalse(iff.isSimplified());
    assertTrue(iff.simplify().equals(new NBVar(x)));

    // y <--> (x <--> False) -- the second part is simplified without affecting the first
    iff = new Iff(y, new Iff(x, new Falsehood()));
    assertFalse(iff.isSimplified());
    assertTrue(iff.simplify().equals(new Iff(x.negate(), y)));
  }

  @Test
  public void testSimplifyTwoIncompatibleSides() {
    BVar x = new BVar(3);
    IVar y = new IVar(7);
    IntegerExpression e = y.add(1);

    // x <--> !x becomes false
    Iff iff = new Iff(x, x.negate());
    assertFalse(iff.isSimplified());
    assertTrue(iff.simplify().equals(new Falsehood()));
    
    // x = 0 <--> x # 0 becomes false
    iff = new Iff(new Neq0(e), new Is0(e));
    assertFalse(iff.isSimplified());
    assertTrue(iff.simplify().equals(new Falsehood()));
  }

  @Test
  public void testSimplifyWithGeq() {
    IVar y = new IVar(7, "y");
    IntegerExpression e = y.add(-1);

    // y = 0 <--> y - 1 ≥ 0 (because y < y - 1 in the IntegerExpression ordering)
    Iff iff = new Iff(new Is0(y), new Geq0(e));
    assertTrue(iff.isSimplified());

    // y - 1 ≥ 0 <--> y - 1 = 0 is equivalent to y - 1 ≤ 0, so -y + 1 ≥ 0, so 1 ≥ y
    iff = new Iff(new Is0(e), new Geq0(e));
    assertFalse(iff.isSimplified());
    assertTrue(iff.simplify().toString().equals("1 >= [y]"));

    // z # 0 <--> y - 1 ≥ 0 is simplified;
    // y - 1 ≥ 0 <--> z # 0 is simplified except for the reordin
    iff = new Iff(new Geq0(e), new Neq0(new IVar(12)));
    assertFalse(iff.isSimplified());
    Constraint iff2 = iff.simplify();
    assertTrue(iff2.toString().equals("(i12 # 0) == ([y] >= 1)"));
    assertTrue(iff2.isSimplified());

    // y - 1 ≥ 0 <--> y - 1 # 0 is equivalent to y - 1 > 0, so y ≥ 2
    iff = new Iff(new Geq0(e), new Neq0(e));
    assertFalse(iff.isSimplified());
    assertTrue(iff.simplify().toString().equals("[y] >= 2"));
  }

  @Test
  public void testNegateSimplified() {
    // x = 0 <--> y ≥ 0
    IVar x = new IVar(3, "x");
    IVar y = new IVar(7, "y");
    Constraint tmp = new Is0(x);
    Iff iff = new Iff(new Is0(x), new Geq0(y));
    Constraint neg = iff.negate();
    assertTrue(iff.isSimplified());
    assertTrue(iff.toString().equals("([x] = 0) == ([y] >= 0)"));
    assertTrue(neg.isSimplified());
    assertTrue(neg.toString().equals("([x] # 0) == ([y] >= 0)"));
  }
}

