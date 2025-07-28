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

package charlie.terms;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;
import charlie.types.TypeFactory;
import charlie.types.Type;

public class ConnectiveTest extends TermTestFoundation {
  @Test
  public void testAndBasics() {
    CalculationSymbol a = TheoryFactory.andSymbol;
    assertTrue(a.queryType().toString().equals("Bool → Bool → Bool"));
    assertTrue(a.queryInfixPriority() == CalculationSymbol.INFIX_ANDOR);
    assertTrue(a.queryName().equals("∧"));
    assertTrue(a.toString().equals("[∧]"));
    assertTrue(a.toUniqueString().equals("∧{Bool → Bool → Bool}#calc"));
    assertTrue(a.queryArity() == 2);
  }

  @Test
  public void testOrBasics() {
    CalculationSymbol o = TheoryFactory.orSymbol;
    assertTrue(o.queryType().toString().equals("Bool → Bool → Bool"));
    assertTrue(o.queryInfixPriority() == CalculationSymbol.INFIX_ANDOR);
    assertTrue(o.queryName().equals("∨"));
    assertTrue(o.toString().equals("[∨]"));
    assertTrue(o.toUniqueString().equals("∨{Bool → Bool → Bool}#calc"));
    assertTrue(o.queryArity() == 2);
  }

  @Test
  public void testNotBasics() {
    CalculationSymbol o = TheoryFactory.notSymbol;
    assertTrue(o.queryType().toString().equals("Bool → Bool"));
    assertTrue(o.queryInfixPriority() == CalculationSymbol.INFIX_NONE);
    assertTrue(o.queryName().equals("¬"));
    assertTrue(o.toString().equals("[¬]"));
    assertTrue(o.toUniqueString().equals("¬{Bool → Bool}#calc"));
    assertTrue(o.queryArity() == 1);
  }

  @Test
  public void testIffBasics() {
    CalculationSymbol o = TheoryFactory.iffSymbol;
    assertTrue(o.queryType().toString().equals("Bool → Bool → Bool"));
    assertTrue(o.queryInfixPriority() == CalculationSymbol.INFIX_IFF);
    assertTrue(o.queryName().equals("⇔"));
    assertTrue(o.toString().equals("[⇔]"));
    assertTrue(o.toUniqueString().equals("⇔{Bool → Bool → Bool}#calc"));
    assertTrue(o.queryArity() == 2);
  }

  @Test
  public void testXorBasics() {
    CalculationSymbol o = TheoryFactory.xorSymbol;
    assertTrue(o.queryType().toString().equals("Bool → Bool → Bool"));
    assertTrue(o.queryInfixPriority() == CalculationSymbol.INFIX_IFF);
    assertTrue(o.queryName().equals("⊻"));
    assertTrue(o.toString().equals("[⊻]"));
    assertTrue(o.toUniqueString().equals("⊻{Bool → Bool → Bool}#calc"));
    assertTrue(o.queryArity() == 2);
  }

  @Test
  public void testSimpleAndToString() {
    CalculationSymbol f = TheoryFactory.andSymbol;
    assertTrue(f.toString().equals("[∧]"));
    Value v = new BooleanValue(true);
    assertTrue(f.apply(v).toString().equals("[∧](true)"));
    Value w = new BooleanValue(false);
    assertTrue(f.apply(List.of(v, w)).toString().equals("true ∧ false"));
  }

  @Test
  public void testSimpleOrToString() {
    CalculationSymbol f = TheoryFactory.orSymbol;
    assertTrue(f.toString().equals("[∨]"));
    Term v = new Var("x", TypeFactory.boolSort);
    assertTrue(f.apply(v).toString().equals("[∨](x)"));
    Value w = new BooleanValue(true);
    assertTrue(f.apply(List.of(v,w)).toString().equals("x ∨ true"));
  }

  @Test
  public void testSimpleNotToString() {
    CalculationSymbol f = TheoryFactory.notSymbol;
    assertTrue(f.toString().equals("[¬]"));
    Term v = new Var("x", TypeFactory.boolSort);
    assertTrue(f.apply(v).toString().equals("¬x"));
  }

  @Test
  public void testSimpleIffToString() {
    CalculationSymbol f = TheoryFactory.iffSymbol;
    assertTrue(f.toString().equals("[⇔]"));
    Value v = new BooleanValue(true);
    assertTrue(f.apply(v).toString().equals("[⇔](true)"));
    Value w = new BooleanValue(false);
    assertTrue(f.apply(List.of(v,w)).toString().equals("true ⇔ false"));
  }

  @Test
  public void testSimpleXorToString() {
    CalculationSymbol f = TheoryFactory.xorSymbol;
    assertTrue(f.toString().equals("[⊻]"));
    Value v = new BooleanValue(true);
    assertTrue(f.apply(v).toString().equals("[⊻](true)"));
    Value w = new BooleanValue(false);
    assertTrue(f.apply(List.of(v,w)).toString().equals("true ⊻ false"));
  }

  @Test
  public void testDoubleNotToString() {
    CalculationSymbol f = TheoryFactory.notSymbol;
    Term v = new BooleanValue(true);
    Term s = f.apply(f.apply(v));
    assertTrue(s.toString().equals("¬(¬true)"));
  }

  @Test
  public void testAndLeftAssociative() {
    Var x = new Var("x", TypeFactory.boolSort);
    Var y = new Var("y", TypeFactory.boolSort);
    Var z = new Var("z", TypeFactory.boolSort);
    CalculationSymbol a = TheoryFactory.andSymbol;
    Term s = new Application(a, new Application(a, x, y), z);
    assertTrue(s.toString().equals("x ∧ y ∧ z"));
  }

  @Test
  public void testOrNotRightAssociative() {
    Var x = new Var("x", TypeFactory.boolSort);
    Var y = new Var("y", TypeFactory.boolSort);
    Var z = new Var("z", TypeFactory.boolSort);
    CalculationSymbol o = TheoryFactory.orSymbol;
    Term s = new Application(o, x, new Application(o, y, z));
    assertTrue(s.toString().equals("x ∨ (y ∨ z)"));
  }

  @Test
  public void testNotInAndInOr() {
    Var x = new Var("x", TypeFactory.boolSort);
    Var y = new Var("y", TypeFactory.boolSort);
    Term notx = new Application(TheoryFactory.notSymbol, x);
    CalculationSymbol a = TheoryFactory.andSymbol;
    CalculationSymbol o = TheoryFactory.orSymbol;
    Term s = new Application(o, new Application(a, notx, y), new Application(a, y, notx));
    assertTrue(s.toString().equals("(¬x ∧ y) ∨ (y ∧ ¬x)"));
  }

  @Test
  public void testOrInAndInNot() {
    Var x = new Var("x", TypeFactory.boolSort);
    Var y = new Var("y", TypeFactory.boolSort);
    CalculationSymbol a = TheoryFactory.andSymbol;
    CalculationSymbol o = TheoryFactory.orSymbol;
    CalculationSymbol n = TheoryFactory.notSymbol;
    Term s = new Application(a, new Application(o, x, y), new Application(o, y, x));
    Term t = new Application(n, s);
    assertTrue(t.toString().equals("¬((x ∨ y) ∧ (y ∨ x))"));
  }

  @Test
  public void testIffAndXorNotAssociative() {
    Var x = new Var("x", TypeFactory.boolSort);
    Var y = new Var("y", TypeFactory.boolSort);
    Var z = new Var("z", TypeFactory.boolSort);
    CalculationSymbol i = TheoryFactory.iffSymbol;
    CalculationSymbol o = TheoryFactory.xorSymbol;

    Term xy_z = i.apply(List.of(i.apply(List.of(x, y)), z));
    Term x_yz = i.apply(List.of(x, i.apply(List.of(y, z))));
    assertTrue(xy_z.toString().equals("(x ⇔ y) ⇔ z"));
    assertTrue(x_yz.toString().equals("x ⇔ (y ⇔ z)"));

    xy_z = o.apply(List.of(o.apply(List.of(x, y)), z));
    x_yz = o.apply(List.of(x, o.apply(List.of(y, z))));
    assertTrue(xy_z.toString().equals("(x ⊻ y) ⊻ z"));
    assertTrue(x_yz.toString().equals("x ⊻ (y ⊻ z)"));

    xy_z = o.apply(List.of(i.apply(List.of(x, y)), z));
    x_yz = i.apply(List.of(x, o.apply(List.of(y, z))));
    assertTrue(xy_z.toString().equals("(x ⇔ y) ⊻ z"));
    assertTrue(x_yz.toString().equals("x ⇔ (y ⊻ z)"));
  }

  @Test
  public void testAndOrInIffXor() {
    Var x = new Var("x", TypeFactory.boolSort);
    Var y = new Var("y", TypeFactory.boolSort);
    CalculationSymbol a = TheoryFactory.andSymbol;
    CalculationSymbol o = TheoryFactory.orSymbol;
    Term s = a.apply(List.of(x, y));
    Term t = o.apply(List.of(x, y));
    Term q = TheoryFactory.iffSymbol.apply(List.of(s, t));
    assertTrue(q.toString().equals("x ∧ y ⇔ x ∨ y"));
    q = TheoryFactory.xorSymbol.apply(List.of(s, t));
    assertTrue(q.toString().equals("x ∧ y ⊻ x ∨ y"));
  }

  @Test
  public void testIffXorInnd() {
    Var x = new Var("x", TypeFactory.boolSort);
    Var y = new Var("y", TypeFactory.boolSort);
    CalculationSymbol a = TheoryFactory.andSymbol;
    CalculationSymbol i = TheoryFactory.iffSymbol;
    CalculationSymbol o = TheoryFactory.xorSymbol;
    Term q = a.apply(List.of(i.apply(List.of(x, y)), o.apply(List.of(y, x))));
    assertTrue(q.toString().equals("(x ⇔ y) ∧ (y ⊻ x)"));
  }

  @Test
  public void testIffWithNot() {
    Var x = new Var("x", TypeFactory.boolSort);
    Var y = new Var("y", TypeFactory.boolSort);
    Term s = TheoryFactory.andSymbol.apply(List.of(x, y));
    Term t = TheoryFactory.notSymbol.apply(s);
    Term u = TheoryFactory.iffSymbol.apply(List.of(s, t));
    Term q = TheoryFactory.notSymbol.apply(u);
    assertTrue(q.toString().equals("¬(x ∧ y ⇔ ¬(x ∧ y))"));
  }

  @Test
  public void testAndOrEquality() {
    FunctionSymbol a = TheoryFactory.andSymbol;
    FunctionSymbol o = TheoryFactory.orSymbol;
    Type b = TypeFactory.boolSort;
    FunctionSymbol fakeand = new Constant("∧", arrowType(b, arrowType(b, b)));
    assertTrue(a.equals(TheoryFactory.andSymbol));
    assertFalse(a.equals(o));
    assertFalse(a.equals(fakeand));
    assertFalse(fakeand.equals(a));
  }

  @Test
  public void testNotEquality() {
    FunctionSymbol n = TheoryFactory.notSymbol;
    FunctionSymbol fakenot =
      new Constant("¬", arrowType(TypeFactory.boolSort, TypeFactory.boolSort));
    assertTrue(n.equals(n));
    assertFalse(n.equals(TheoryFactory.orSymbol));
    assertFalse(n.equals(fakenot));
    assertFalse(fakenot.equals(n));
  }

  @Test
  public void testIffEquality() {
    FunctionSymbol i = TheoryFactory.iffSymbol;
    FunctionSymbol o = TheoryFactory.orSymbol;
    Type b = TypeFactory.boolSort;
    FunctionSymbol fakeiff = new Constant("⇔", arrowType(b, arrowType(b, b)));
    assertTrue(i.equals(TheoryFactory.iffSymbol));
    assertFalse(i.equals(o));
    assertFalse(i.equals(fakeiff));
  }
}
