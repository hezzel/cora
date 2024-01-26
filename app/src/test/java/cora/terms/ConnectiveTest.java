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

package cora.terms;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.exceptions.*;
import cora.types.TypeFactory;
import cora.types.Type;

public class ConnectiveTest extends TermTestFoundation {
  @Test
  public void testAndBasics() {
    CalculationSymbol a = new AndOrSymbol(false);
    assertTrue(a.queryType().toString().equals("Bool → Bool → Bool"));
    assertTrue(a.queryInfixPriority() == CalculationSymbol.INFIX_ANDOR);
    assertTrue(a.queryName().equals("∧"));
    assertTrue(a.toString().equals("∧"));
    assertTrue(a.toUniqueString().equals("∧"));
    assertTrue(a.queryArity() == 2);
  }

  @Test
  public void testOrBasics() {
    CalculationSymbol o = new AndOrSymbol(true);
    assertTrue(o.queryType().toString().equals("Bool → Bool → Bool"));
    assertTrue(o.queryInfixPriority() == CalculationSymbol.INFIX_ANDOR);
    assertTrue(o.queryName().equals("∨"));
    assertTrue(o.toString().equals("∨"));
    assertTrue(o.toUniqueString().equals("∨"));
    assertTrue(o.queryArity() == 2);
  }

  @Test
  public void testNotBasics() {
    CalculationSymbol o = new NotSymbol();
    assertTrue(o.queryType().toString().equals("Bool → Bool"));
    assertTrue(o.queryInfixPriority() == CalculationSymbol.INFIX_NOT);
    assertTrue(o.queryName().equals("¬"));
    assertTrue(o.toString().equals("¬"));
    assertTrue(o.toUniqueString().equals("¬"));
    assertTrue(o.queryArity() == 1);
  }

  @Test
  public void testSimpleAndToString() {
    CalculationSymbol f = new AndOrSymbol(false);
    assertTrue(f.toString().equals("∧"));
    Value v = new BooleanValue(true);
    assertTrue(f.apply(v).toString().equals("∧(true)"));
    Value w = new BooleanValue(false);
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(v);
    args.add(w);
    assertTrue(f.apply(args).toString().equals("true ∧ false"));
  }

  @Test
  public void testSimpleOrToString() {
    CalculationSymbol f = new AndOrSymbol(true);
    assertTrue(f.toString().equals("∨"));
    Term v = new Var("x", TypeFactory.boolSort);
    assertTrue(f.apply(v).toString().equals("∨(x)"));
    Value w = new BooleanValue(true);
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(v);
    args.add(w);
    assertTrue(f.apply(args).toString().equals("x ∨ true"));
  }

  @Test
  public void testSimpleNotToString() {
    CalculationSymbol f = new NotSymbol();
    assertTrue(f.toString().equals("¬"));
    Term v = new Var("x", TypeFactory.boolSort);
    assertTrue(f.apply(v).toString().equals("¬x"));
  }

  @Test
  public void testDoubleNotToString() {
    CalculationSymbol f = new NotSymbol();
    Term v = new BooleanValue(true);
    Term s = f.apply(f.apply(v));
    assertTrue(s.toString().equals("¬(¬true)"));
  }

  @Test
  public void testAndLeftAssociative() {
    Var x = new Var("x", TypeFactory.boolSort);
    Var y = new Var("y", TypeFactory.boolSort);
    Var z = new Var("z", TypeFactory.boolSort);
    CalculationSymbol a = new AndOrSymbol(false);
    Term s = new Application(a, new Application(a, x, y), z);
    assertTrue(s.toString().equals("x ∧ y ∧ z"));
  }

  @Test
  public void testOrNotRightAssociative() {
    Var x = new Var("x", TypeFactory.boolSort);
    Var y = new Var("y", TypeFactory.boolSort);
    Var z = new Var("z", TypeFactory.boolSort);
    CalculationSymbol o = new AndOrSymbol(true);
    Term s = new Application(o, x, new Application(o, y, z));
    assertTrue(s.toString().equals("x ∨ (y ∨ z)"));
  }

  @Test
  public void testNotInAndInOr() {
    Var x = new Var("x", TypeFactory.boolSort);
    Var y = new Var("y", TypeFactory.boolSort);
    Term notx = new Application(new NotSymbol(), x);
    CalculationSymbol a = new AndOrSymbol(false);
    CalculationSymbol o = new AndOrSymbol(true);
    Term s = new Application(o, new Application(a, notx, y), new Application(a, y, notx));
    assertTrue(s.toString().equals("(¬x ∧ y) ∨ (y ∧ ¬x)"));
  }

  @Test
  public void testOrInAndInNot() {
    Var x = new Var("x", TypeFactory.boolSort);
    Var y = new Var("y", TypeFactory.boolSort);
    CalculationSymbol a = new AndOrSymbol(false);
    CalculationSymbol o = new AndOrSymbol(true);
    CalculationSymbol n = new NotSymbol();
    Term s = new Application(a, new Application(o, x, y), new Application(o, y, x));
    Term t = new Application(n, s);
    assertTrue(t.toString().equals("¬((x ∨ y) ∧ (y ∨ x))"));
  }

  @Test
  public void testAndOrEquality() {
    FunctionSymbol a = new AndOrSymbol(false);
    FunctionSymbol o = new AndOrSymbol(true);
    Type b = TypeFactory.boolSort;
    FunctionSymbol fakeand = new Constant("∧", arrowType(b, arrowType(b, b)));
    assertTrue(a.equals(new AndOrSymbol(false)));
    assertFalse(a.equals(o));
    assertFalse(a.equals(fakeand));
    assertFalse(fakeand.equals(a));
  }

  @Test
  public void testNotEquality() {
    FunctionSymbol n = new NotSymbol();
    FunctionSymbol fakenot =
      new Constant("¬", arrowType(TypeFactory.boolSort, TypeFactory.boolSort));
    assertTrue(n.equals(n));
    assertFalse(n.equals(new AndOrSymbol(true)));
    assertFalse(n.equals(fakenot));
    assertFalse(fakenot.equals(n));
  }
}
