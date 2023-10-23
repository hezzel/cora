/**************************************************************************************************
 Copyright 2022, 2023 Cynthia Kop

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

import cora.exceptions.IllegalArgumentError;
import cora.exceptions.IncorrectStringException;
import cora.types.BaseType;

/**
 * A factory only to create logical terms and symbols
 *
 * Note: all theory symbols (values and calculation symbols) necessarily have a translation in
 * SMT.  Thus, when adding any function symbol here, also add them into the translator functionality
 * in smt.TermSmtTranslator and smt.TermAnalyser.
 */
public class TheoryFactory {
  /** Create a non-binder variable with the given name and base sort. */
  public static Variable createVar(String name, BaseType type) {
    if (!type.isTheorySort()) {
      throw new IllegalArgumentError("TheoryFactory", "createVar", "given type " +
        type.toString() + " is not a theory sort.");
    }
    return new Var(name, type);
  }

  /** Create an Integer Value */
  public static Value createValue(int n) {
    return new IntegerValue(n);
  }

  /** Create a Boolean Value */
  public static Value createValue(boolean b) {
    return new BooleanValue(b);
  }

  /** Create a String Value */
  public static Value createValue(String s) {
    return new StringValue(s);
  }

  /** Create a String Value with a string in quotes, and potentially with escape characters in it */
  public static Value createEscapedStringValue(String s) throws IncorrectStringException {
    return StringValue.parseUserStringValue(s);
  }

  /** The binary symbol for addition */
  public static CalculationSymbol plusSymbol = new PlusSymbol();

  /** The binary symbol for multiplication */
  public static CalculationSymbol timesSymbol = new TimesSymbol();
  
  /** The unary(!) symbol for integer negation */
  public static CalculationSymbol minusSymbol = new MinusSymbol();

  /** The binary calculation symbol for conjunction */
  public static CalculationSymbol andSymbol = new AndOrSymbol(false);

  /** The binary calculation symbol for disjunction */
  public static CalculationSymbol orSymbol = new AndOrSymbol(true);

  /** The unary calculation symbol for boolean negation */
  public static CalculationSymbol notSymbol = new NotSymbol();

  /** The binary calculation symbol for greater */
  public static CalculationSymbol greaterSymbol = new ComparisonSymbol(ComparisonSymbol.KIND_GRE);

  /** The binary calculation symbol for smaller. */
  public static CalculationSymbol smallerSymbol = new ComparisonSymbol(ComparisonSymbol.KIND_SMA);

  /** The binary calculation symbol for greater-than-or-equal-to */
  public static CalculationSymbol geqSymbol = new ComparisonSymbol(ComparisonSymbol.KIND_GEQ);

  /** The binary calculation symbol for smaller-than-or-equal-to */
  public static CalculationSymbol leqSymbol = new ComparisonSymbol(ComparisonSymbol.KIND_LEQ);

  /** The binary calculation symbol for equality */
  public static CalculationSymbol equalSymbol = new ComparisonSymbol(ComparisonSymbol.KIND_EQU);

  /** The binary calculation symbol for inequality */
  public static CalculationSymbol distinctSymbol = new ComparisonSymbol(ComparisonSymbol.KIND_NEQ);
}

