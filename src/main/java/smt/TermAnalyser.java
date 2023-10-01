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
import cora.terms.Value;
import cora.terms.TheoryFactory;

/**
 * This class provides analysis functions on theory terms, by using a translation to SMT.
 */
public class TermAnalyser {
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
    if (t.queryType().equals(TypeFactory.intSort)) {
      IntegerExpression e = TermSmtTranslator.translateIntegerExpression(t);
      return TheoryFactory.createValue(e.evaluate());
    }
    if (t.queryType().equals(TypeFactory.boolSort)) {
      Constraint c = TermSmtTranslator.translateConstraint(t);
      return TheoryFactory.createValue(c.evaluate());
    }
    throw new UnsupportedTheoryError(t.toString(), "Type " + t.queryType().toString() + " is " +
      "not a supported theory sort.");
  }
}

