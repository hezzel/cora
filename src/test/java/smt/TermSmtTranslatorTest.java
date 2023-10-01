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

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.exceptions.UnsupportedTheoryError;
import cora.types.Type;
import cora.types.TypeFactory;
import cora.terms.Term;
import cora.terms.Variable;
import cora.terms.TermFactory;
import cora.terms.TheoryFactory;
import cora.rewriting.TRS;
import cora.parsing.CoraInputReader;

public class TermSmtTranslatorTest {
  private TRS _trs = null;

  @Test
  public void testTranslateIntegerValue() {
    Term t = TheoryFactory.createValue(-37);
    IntegerExpression e = TermSmtTranslator.translateIntegerExpression(t);
    assertTrue(e instanceof IValue);
    assertTrue(e.toString().equals("(- 37)"));
  }

  @Test
  public void testTranslateVariable() {
    Term t = TheoryFactory.createVar("x", TypeFactory.intSort);
    IntegerExpression e = TermSmtTranslator.translateIntegerExpression(t);
    assertTrue(e instanceof IVar);
    assertTrue(e.toString().equals("i" + t.queryVariable().queryIndex()));
  }

  @Test
  public void testTranslatePlus() {
    // 1 + (x + 3)
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term t = TheoryFactory.plusSymbol.apply(TheoryFactory.createValue(1)).apply(
      TheoryFactory.plusSymbol.apply(x).apply(TheoryFactory.createValue(3)));
    IntegerExpression e = TermSmtTranslator.translateIntegerExpression(t);
    assertTrue(e instanceof Addition);
    assertTrue(e.toString().equals("(+ 1 i" + x.queryIndex() + " 3)"));
  }

  @Test
  public void testTranslateMinus() {
    // - x
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term t = TheoryFactory.minusSymbol.apply(x);
    IntegerExpression e = TermSmtTranslator.translateIntegerExpression(t);
    assertTrue(e instanceof Minus);
    assertTrue(e.toString().equals("(- i" + x.queryIndex() + ")"));
  }

  @Test
  public void testTranslateTimes() {
    // (3 * (x + 1)) * y
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Term t = TheoryFactory.timesSymbol.apply(
      TheoryFactory.timesSymbol.apply(TheoryFactory.createValue(3)).apply(
        TheoryFactory.plusSymbol.apply(x).apply(TheoryFactory.createValue(1)))
    ).apply(y);
    IntegerExpression e = TermSmtTranslator.translateIntegerExpression(t);
    assertTrue(e instanceof Multiplication);
    assertTrue(e.toString().equals("(* 3 (+ i" + x.queryIndex() + " 1) i" + y.queryIndex() + ")"));
  }

  @Test
  public void testTranslateComplexIntegerExpression() {
    // x - (-1 - y)
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Term t = TheoryFactory.plusSymbol.apply(x).apply(TheoryFactory.minusSymbol.apply(
      TheoryFactory.plusSymbol.apply(TheoryFactory.createValue(-1)).apply(
      TheoryFactory.minusSymbol.apply(y))));
    IntegerExpression e = TermSmtTranslator.translateIntegerExpression(t);
    assertTrue(e.toString().equals("(+ i" + x.queryIndex() + " (- (+ (- 1) " +
      "(- i" + y.queryIndex() + "))))"));
  }

  @Test(expected = UnsupportedTheoryError.class)
  public void testNonIntTranslateInteger() {
    TermSmtTranslator.translateIntegerExpression(TheoryFactory.createVar("x", TypeFactory.boolSort));
  }

  @Test(expected = UnsupportedTheoryError.class)
  public void testNonCalcTranslateInteger() {
    Type is = TypeFactory.intSort;
    Term f = TermFactory.createConstant("+",
      TypeFactory.createArrow(is, TypeFactory.createArrow(is, is)));
    Term t = f.apply(TheoryFactory.createValue(7)).apply(TheoryFactory.createValue(8));
    TermSmtTranslator.translateIntegerExpression(t);
  }

  @Test
  public void testTranslateAnd() {
    // x ∧ true
    Variable x = TheoryFactory.createVar("x", TypeFactory.boolSort);
    Term t = TheoryFactory.andSymbol.apply(x).apply(TheoryFactory.createValue(true));
    Constraint c = TermSmtTranslator.translateConstraint(t);
    assertTrue(c.toString().equals("(and b" + x.queryIndex() + " true)"));
  }

  @Test
  public void testTranslateOr() {
    // true ∨ false
    Term t = TheoryFactory.orSymbol.apply(TheoryFactory.createValue(true)).apply(
      TheoryFactory.createValue(false));
    Constraint c = TermSmtTranslator.translateConstraint(t);
    assertTrue(c.toString().equals("(or true false)"));
  }

  @Test
  public void testTranslateNot() {
    // ¬ x
    Variable x = TheoryFactory.createVar("x", TypeFactory.boolSort);
    Term t = TheoryFactory.notSymbol.apply(x);
    Constraint c = TermSmtTranslator.translateConstraint(t);
    assertTrue(c.toString().equals("(not b" + x.queryIndex() + ")"));
  }

  @Test
  public void testTranslateGreater() {
    // 1 > x
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term t = TheoryFactory.greaterSymbol.apply(TheoryFactory.createValue(1)).apply(x);
    Constraint c = TermSmtTranslator.translateConstraint(t);
    assertTrue(c.toString().equals("(> 1 i" + x.queryIndex() + ")"));
  }

  @Test
  public void testTranslateSmaller() {
    // 1 < x
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term t = TheoryFactory.smallerSymbol.apply(TheoryFactory.createValue(1)).apply(x);
    Constraint c = TermSmtTranslator.translateConstraint(t);
    assertTrue(c.toString().equals("(> i" + x.queryIndex() + " 1)"));
  }

  @Test
  public void testTranslateGeq() {
    // x ≥ 2
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term t = TheoryFactory.geqSymbol.apply(x).apply(TheoryFactory.createValue(2));
    Constraint c = TermSmtTranslator.translateConstraint(t);
    assertTrue(c.toString().equals("(>= i" + x.queryIndex() + " 2)"));
  }

  @Test
  public void testTranslateLeq() {
    // 3 ≤ 2
    Term t = TheoryFactory.leqSymbol.apply(TheoryFactory.createValue(3)).apply(
      TheoryFactory.createValue(2));
    Constraint c = TermSmtTranslator.translateConstraint(t);
    assertTrue(c.toString().equals("(>= 2 3)"));
  }

  @Test
  public void testTranslateComplexConstraint() {
    // x > 3 ∧ ((2 ≤ 5 ∨ y) ∧ true)
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.boolSort);
    Term t1 = TheoryFactory.greaterSymbol.apply(x).apply(TheoryFactory.createValue(3));
    Term t2 = TheoryFactory.leqSymbol.apply(TheoryFactory.createValue(2)).apply(
      TheoryFactory.createValue(5));
    Term t3 = TheoryFactory.andSymbol.apply(TheoryFactory.orSymbol.apply(t2).apply(y)).apply(
      TheoryFactory.createValue(true));
    Term t = TheoryFactory.andSymbol.apply(t1).apply(t3);
    Constraint c = TermSmtTranslator.translateConstraint(t);
    assertTrue(c.toString().equals("(and (> i" + x.queryIndex() + " 3) (or (>= 5 2) b" +
      y.queryIndex() + ") true)"));
  }

  @Test(expected = UnsupportedTheoryError.class)
  public void testNonBoolTranslateConstraint() {
    TermSmtTranslator.translateIntegerExpression(TheoryFactory.createValue("true"));
  }

  @Test(expected = UnsupportedTheoryError.class)
  public void testNonCalcTranslateConstraint() {
    Type bs = TypeFactory.boolSort;
    Term f = TermFactory.createConstant("∧",
      TypeFactory.createArrow(bs, TypeFactory.createArrow(bs, bs)));
    Term t = f.apply(TheoryFactory.createValue(true)).apply(TheoryFactory.createValue(false));
    TermSmtTranslator.translateConstraint(t);
  }
}

