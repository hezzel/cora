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

package cora.theorytranslation;

import java.util.Random;

import charlie.exceptions.UnsupportedTheoryError;
import charlie.types.Type;
import charlie.types.TypeFactory;
import cora.terms.*;
import charlie.smt.*;
import charlie.smt.SmtSolver.Answer;

/**
 * This class provides analysis functions on theory terms, by using a translation to SMT.
 */
public class TermAnalyser {
  private static Random _rnd = new Random();

  /** Returns a randomly selected value of the given type */
  public static Value chooseRandomValue(Type type) {
    int r = _rnd.nextInt();
    if (type.equals(TypeFactory.intSort)) return TheoryFactory.createValue(r);
    if (type.equals(TypeFactory.boolSort)) return TheoryFactory.createValue((r % 2) == 0);
    if (type.equals(TypeFactory.stringSort)) return TheoryFactory.createValue("{" + r + "}");
    throw new UnsupportedTheoryError("variable", "Asked to choose random value of type " +
      type.toString() + ", which is not a supported theory sort.");
  }

  /** Given a ground theory term, this fully evaluates it to a Value. */
  public static Value evaluate(Term t) {
    TermSmtTranslator translator = new TermSmtTranslator();
    if (t.queryType().equals(TypeFactory.intSort)) {
      IntegerExpression e = translator.translateIntegerExpression(t);
      return TheoryFactory.createValue(e.evaluate());
    }
    if (t.queryType().equals(TypeFactory.boolSort)) {
      Constraint c = translator.translateConstraint(t);
      return TheoryFactory.createValue(c.evaluate());
    }
    if (t.isValue()) return t.toValue();
    throw new UnsupportedTheoryError(t.toString(), "Type " + t.queryType().toString() + " is " +
      "not a supported theory sort.");
  }

  /**
   * Given a term that is a calculation symbol applied to a number of values, this returns the
   * value it reduces to.  If the term has any other form, null is returned.
   * If it is an unknown calculation symbol, or has an unknown type, then an UnsupportedTheoryError
   * is thrown.
   */
  public static Value calculate(Term t) {
    if (!t.isFunctionalTerm() || t.queryRoot().toCalculationSymbol() == null) return null;
    for (int i = 1; i <= t.numberArguments(); i++) {
      if (!t.queryArgument(i).isValue()) return null;
    }
    return evaluate(t);
  }

  /**
   * Given a theory term of type Bool, this function tries to find an assignment for the variables
   * in it that makes the term evaluate to true.  If successful, this substitution is returned; if
   * not, null is returned.
   */
  public static Substitution satisfy(Term t, SmtSolver solver) {
    TermSmtTranslator translator = new TermSmtTranslator();
    translator.require(t);
    switch (solver.checkSatisfiability(translator.queryProblem())) {
      case Answer.YES(Valuation val):
        Substitution ret = TermFactory.createEmptySubstitution();
        for (Variable x : t.vars()) {
          if (x.queryType().equals(TypeFactory.boolSort)) {
            ret.extend(x, TheoryFactory.createValue(val.queryBoolAssignment(x.queryIndex())));
          }
          else if (x.queryType().equals(TypeFactory.intSort)) {
            ret.extend(x, TheoryFactory.createValue(val.queryIntAssignment(x.queryIndex())));
          }
        }
        return ret;
      default:
        return null;
    }
  }
}

