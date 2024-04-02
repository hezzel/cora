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

package charlie.theorytranslation;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import charlie.exceptions.UnsupportedTheoryError;
import charlie.exceptions.TypingError;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.TermFactory;
import charlie.terms.TheoryFactory;
import charlie.smt.*;

public class TermSmtTranslatorTest {
  @Test
  public void testTranslateIntegerValue() {
    TermSmtTranslator tst = new TermSmtTranslator();
    Term t = TheoryFactory.createValue(-37);
    IntegerExpression e = tst.translateIntegerExpression(t);
    assertTrue(e instanceof IValue);
    assertTrue(e.toString().equals("-37"));
    assertTrue(tst.queryProblem().numberIntegerVariables() == 0);
    assertTrue(tst.queryProblem().numberBooleanVariables() == 0);
  }

  @Test
  public void testTranslateIntegerVariable() {
    TermSmtTranslator tst = new TermSmtTranslator();
    Term t = TheoryFactory.createVar("x", TypeFactory.intSort);
    IntegerExpression e = tst.translateIntegerExpression(t);
    assertTrue(e instanceof IVar);
    assertTrue(e.toString().equals("i1"));
    assertTrue(tst.queryProblem().numberIntegerVariables() == 1);
    assertTrue(tst.queryProblem().numberBooleanVariables() == 0);
  }

  @Test
  public void testTranslatePlus() {
    TermSmtTranslator tst = new TermSmtTranslator();
    // 1 + (x + 3)
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term t = TheoryFactory.plusSymbol.apply(TheoryFactory.createValue(1)).apply(
      TheoryFactory.plusSymbol.apply(x).apply(TheoryFactory.createValue(3)));
    IntegerExpression e = tst.translateIntegerExpression(t);
    assertTrue(e instanceof Addition);
    assertTrue(e.toString().equals("1 + i1 + 3"));
  }

  @Test
  public void testTranslateMinus() {
    TermSmtTranslator tst = new TermSmtTranslator();
    // - x
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term t = TheoryFactory.minusSymbol.apply(x);
    IntegerExpression e = tst.translateIntegerExpression(t);
    assertTrue(e instanceof CMult);
    assertTrue(e.toString().equals("-i1"));
  }

  @Test
  public void testTranslateTimes() {
    TermSmtTranslator tst = new TermSmtTranslator();
    // (3 * (x + 1)) * y
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term t = TheoryFactory.timesSymbol.apply(
      TheoryFactory.timesSymbol.apply(TheoryFactory.createValue(3)).apply(
        TheoryFactory.plusSymbol.apply(x).apply(TheoryFactory.createValue(1)))
    ).apply(y);
    IntegerExpression e = tst.translateIntegerExpression(t);
    assertTrue(e instanceof Multiplication);
    assertTrue(e.toString().equals("3 * (i1 + 1) * i2"));
  }

  @Test
  public void testTranslateDivMod() {
    TermSmtTranslator tst = new TermSmtTranslator();
    // 3 / (x - 4 % y)
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Term t = TheoryFactory.divSymbol.apply(TheoryFactory.createValue(3))
      .apply(TheoryFactory.plusSymbol.apply(x).apply(TheoryFactory.minusSymbol.apply(
      TheoryFactory.modSymbol.apply(TheoryFactory.createValue(4)).apply(y))));
    IntegerExpression e = tst.translateIntegerExpression(t);
    assertTrue(e instanceof Division);
    assertTrue(e.toString().equals("3 / (i1 + -(4 % i2))"));
  }

  @Test
  public void testTranslateComplexIntegerExpression() {
    TermSmtTranslator tst = new TermSmtTranslator();
    // x - (-1 - y)
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Term t = TheoryFactory.plusSymbol.apply(x).apply(TheoryFactory.minusSymbol.apply(
      TheoryFactory.plusSymbol.apply(TheoryFactory.createValue(-1)).apply(
      TheoryFactory.minusSymbol.apply(y))));
    IntegerExpression e = tst.translateIntegerExpression(t);
    assertTrue(e.toString().equals("i1 + -(-1 + -i2)"));
  }

  @Test
  public void testNonIntTranslateInteger() {
    TermSmtTranslator tst = new TermSmtTranslator();
    assertThrows(TypingError.class,
      () -> tst.translateIntegerExpression(TheoryFactory.createVar("x", TypeFactory.boolSort)));
  }

  @Test
  public void testNonCalcTranslateInteger() {
    TermSmtTranslator tst = new TermSmtTranslator();
    Type is = TypeFactory.intSort;
    Term f = TermFactory.createConstant("+",
      TypeFactory.createArrow(is, TypeFactory.createArrow(is, is)));
    Term t = f.apply(TheoryFactory.createValue(7)).apply(TheoryFactory.createValue(8));
    assertThrows(UnsupportedTheoryError.class,
      () -> tst.translateIntegerExpression(t));
  }

  @Test
  public void testTranslateAnd() {
    TermSmtTranslator tst = new TermSmtTranslator();
    // x ∧ true
    Variable x = TheoryFactory.createVar("x", TypeFactory.boolSort);
    Term t = TheoryFactory.andSymbol.apply(x).apply(TheoryFactory.createValue(true));
    Constraint c = tst.translateConstraint(t);
    assertTrue(c.toString().equals("b1 and true"));
  }

  @Test
  public void testTranslateOr() {
    TermSmtTranslator tst = new TermSmtTranslator();
    // true ∨ false
    Term t = TheoryFactory.orSymbol.apply(TheoryFactory.createValue(true)).apply(
      TheoryFactory.createValue(false));
    Constraint c = tst.translateConstraint(t);
    assertTrue(c.toString().equals("true or false"));
  }

  @Test
  public void testTranslateNot() {
    TermSmtTranslator tst = new TermSmtTranslator();
    // ¬ x
    Variable x = TheoryFactory.createVar("x", TypeFactory.boolSort);
    Term t = TheoryFactory.notSymbol.apply(x);
    Constraint c = tst.translateConstraint(t);
    assertTrue(c.toString().equals("not b1"));
  }

  @Test
  public void testTranslateGreater() {
    TermSmtTranslator tst = new TermSmtTranslator();
    // 1 > x
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term t = TheoryFactory.greaterSymbol.apply(TheoryFactory.createValue(1)).apply(x);
    Constraint c = tst.translateConstraint(t);
    assertTrue(c.toString().equals("0 >= i1"));
  }

  @Test
  public void testTranslateSmaller() {
    TermSmtTranslator tst = new TermSmtTranslator();
    // 1 < x
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term t = TheoryFactory.smallerSymbol.apply(TheoryFactory.createValue(1)).apply(x);
    Constraint c = tst.translateConstraint(t);
    assertTrue(c.toString().equals("i1 >= 2"));
  }

  @Test
  public void testTranslateGeq() {
    TermSmtTranslator tst = new TermSmtTranslator();
    // x ≥ 2
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term t = TheoryFactory.geqSymbol.apply(x).apply(TheoryFactory.createValue(2));
    Constraint c = tst.translateConstraint(t);
    assertTrue(c.toString().equals("i1 >= 2"));
  }

  @Test
  public void testTranslateLeq() {
    TermSmtTranslator tst = new TermSmtTranslator();
    // 3 ≤ 2
    Term t = TheoryFactory.leqSymbol.apply(TheoryFactory.createValue(3)).apply(
      TheoryFactory.createValue(2));
    Constraint c = tst.translateConstraint(t);
    assertTrue(c.toString().equals("0 >= 1"));
  }

  @Test
  public void testTranslateComplexConstraint() {
    TermSmtTranslator tst = new TermSmtTranslator();
    // x > 3 ∧ ((2 ≤ 5 ∨ y) ∧ true)
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.boolSort);
    Term t1 = TheoryFactory.greaterSymbol.apply(x).apply(TheoryFactory.createValue(3));
    Term t2 = TheoryFactory.leqSymbol.apply(TheoryFactory.createValue(2)).apply(
      TheoryFactory.createValue(5));
    Term t3 = TheoryFactory.andSymbol.apply(TheoryFactory.orSymbol.apply(t2).apply(y)).apply(
      TheoryFactory.createValue(true));
    Term t = TheoryFactory.andSymbol.apply(t1).apply(t3);
    Constraint c = tst.translateConstraint(t);
    assertTrue(c.toString().equals("(i1 >= 4) and ((3 >= 0) or b1) and true"));
  }

  @Test
  public void testNonBoolTranslateConstraint() {
    TermSmtTranslator tst = new TermSmtTranslator();
    assertThrows(UnsupportedTheoryError.class, () ->
      tst.translateIntegerExpression(TheoryFactory.createValue("true")));
  }

  @Test
  public void testNonCalcTranslateConstraint() {
    TermSmtTranslator tst = new TermSmtTranslator();
    Type bs = TypeFactory.boolSort;
    Term f = TermFactory.createConstant("∧",
      TypeFactory.createArrow(bs, TypeFactory.createArrow(bs, bs)));
    Term t = f.apply(TheoryFactory.createValue(true)).apply(TheoryFactory.createValue(false));
    assertThrows(UnsupportedTheoryError.class, () ->
      tst.translateConstraint(t));
  }
}

