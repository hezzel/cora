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

import cora.exceptions.UnsupportedTheoryError;
import cora.types.TypeFactory;
import cora.terms.Term;
import cora.terms.FunctionSymbol;
import cora.terms.CalculationSymbol;
import cora.terms.TheoryFactory;

/**
 * This class provides translations between theory terms and SMT expressions.
 */
public class TermSmtTranslator {
  /**
   * Helper function for multiple translate methods; given a term that *should* be a functional
   * term with a calculation as its root, returns that calculation symbol (and throws some errors
   * if the term does not have the expected shape).
   */
  private static CalculationSymbol getCalculationRoot(Term t) {
    if (!t.isFunctionalTerm()) {
      throw new UnsupportedTheoryError(t.toString(), "expected variable or functional term");
    }
    FunctionSymbol root = t.queryRoot();
    CalculationSymbol calc = root.toCalculationSymbol();
    if (calc == null) {
      throw new UnsupportedTheoryError(t.toString(),
                                       "root " + root.toString() + " is not a calculation symbol");
    }
    return calc;
  }

  /**
   * This takes a theory term of type Int, and returns the corresponding IntegerExpression, for use
   * in SMT analysis.
   * The given SmtProblem is used for generating and storing variables.
   */
  public static IntegerExpression translateIntegerExpression(Term t, SmtProblem problem) {
    if (!t.queryType().equals(TypeFactory.intSort)) {
      throw new UnsupportedTheoryError(t.toString(),
                                       "expected integer type, not " + t.queryType().toString());
    }
    if (t.isVariable()) return problem.createIntegerVariable(t.queryVariable().queryIndex());
    if (t.isValue()) return problem.createValue(t.toValue().getInt());
    CalculationSymbol calc = getCalculationRoot(t);
    if (calc.equals(TheoryFactory.minusSymbol)) {
      return problem.createNegation(translateIntegerExpression(t.queryArgument(1), problem));
    }
    if (calc.equals(TheoryFactory.plusSymbol)) {
      return problem.createAddition(translateIntegerExpression(t.queryArgument(1), problem),
                                    translateIntegerExpression(t.queryArgument(2), problem));
    }
    if (calc.equals(TheoryFactory.timesSymbol)) {
      return problem.createMultiplication(translateIntegerExpression(t.queryArgument(1), problem),
                                          translateIntegerExpression(t.queryArgument(2), problem));
    }
    throw new UnsupportedTheoryError(t.toString(),
      "unfamiliar integer calculation symbol: " + calc.queryName());
  }

  /**
   * This takes a theory term of type Bool, and returns the corresponding Constraint, for use in
   * SMT analysis.
   * The given SmtProblem is used for generating and storing variables.
   */
  public static Constraint translateConstraint(Term t, SmtProblem problem) {
    if (!t.queryType().equals(TypeFactory.boolSort)) {
      throw new UnsupportedTheoryError(t.toString(),
                                       "expected boolean type, not " + t.queryType().toString());
    }
    if (t.isVariable()) return problem.createBooleanVariable(t.queryVariable().queryIndex());
    if (t.isValue()) {
      if (t.toValue().getBool()) return problem.createTrue();
      else return problem.createFalse();
    }
    CalculationSymbol calc = getCalculationRoot(t);
    if (calc.equals(TheoryFactory.andSymbol)) {
      return problem.createConjunction(translateConstraint(t.queryArgument(1), problem),
                                       translateConstraint(t.queryArgument(2), problem));
    }
    if (calc.equals(TheoryFactory.orSymbol)) {
      return problem.createDisjunction(translateConstraint(t.queryArgument(1), problem),
                                       translateConstraint(t.queryArgument(2), problem));
    }
    if (calc.equals(TheoryFactory.notSymbol)) {
      return problem.createNegation(translateConstraint(t.queryArgument(1), problem));
    }
    if (calc.equals(TheoryFactory.greaterSymbol)) {
      return problem.createGreater(translateIntegerExpression(t.queryArgument(1), problem),
                                   translateIntegerExpression(t.queryArgument(2), problem));
    }
    if (calc.equals(TheoryFactory.smallerSymbol)) {
      return problem.createSmaller(translateIntegerExpression(t.queryArgument(1), problem),
                                   translateIntegerExpression(t.queryArgument(2), problem));
    }
    if (calc.equals(TheoryFactory.geqSymbol)) {
      return problem.createGeq(translateIntegerExpression(t.queryArgument(1), problem),
                               translateIntegerExpression(t.queryArgument(2), problem));
    }
    if (calc.equals(TheoryFactory.leqSymbol)) {
      return problem.createLeq(translateIntegerExpression(t.queryArgument(1), problem),
                               translateIntegerExpression(t.queryArgument(2), problem));
    }
    if (calc.equals(TheoryFactory.equalSymbol)) {
      return problem.createEqual(translateIntegerExpression(t.queryArgument(1), problem),
                                 translateIntegerExpression(t.queryArgument(2), problem));
    }
    if (calc.equals(TheoryFactory.distinctSymbol)) {
      return problem.createUnequal(translateIntegerExpression(t.queryArgument(1), problem),
                                   translateIntegerExpression(t.queryArgument(2), problem));
    }
    throw new UnsupportedTheoryError(t.toString(),
      "unfamiliar boolean calculation symbol: " + calc.queryName());
  }
}

