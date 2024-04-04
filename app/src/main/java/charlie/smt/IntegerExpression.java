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

import java.lang.Comparable;

/**
 * An IntegerExpression is an expression built from integer values, addition, multiplication, etc.:
 * the symbols in the integer theory, yielding an int.
 *
 * IntegerExpressions can be expected to be immutable.
 */

public sealed abstract class IntegerExpression implements Comparable<IntegerExpression>
  permits IVar, IValue, Division, Modulo, CMult, Multiplication, Addition {

  /**
   * This variable should be set to true in the constructor if the IntegerExpression is simplified.
   * Note that being simplified means that all sub-expressions must also be simplified.
   */
  protected boolean _simplified;

  /**
   * The _simplified variable is set to false by default, but inheriting classes should all set it
   * to true if the class is in fact simplified.
   */
  protected IntegerExpression() {
    _simplified = false;
  }

  /**
   * Assuming the current expression has no variables, this function evaluates it to its integer
   * value.  If there is a variable in it, an SmtEvaluationError will be thrown instead.
   */
  public abstract int evaluate();

  /** Adds the SMT description of the current expression to the given string builder. */
  public abstract void addToSmtString(StringBuilder builder);

  /**
   * This generates a total ordering on integer expressions.  Constants are guaranteed to be minimal
   * in the ordering (compared to expressions that are not constants).
   */
  public abstract int compareTo(IntegerExpression other);

  /**
   * This moves the IntegerExpression into a simplified form.  For the result we have:
   * - in Addition and Multiplication, all components are listed in order
   * - in Addition, components are combined if possible (e.g., x + x is turned into 2 * x)
   * - in CMult, the constant is not 0 or 1
   * - in Division and Modulo, the denominator is not 1
   * - Addition does not occur below Addition, Multiplication or CMult
   * - CMult does not occur below Multiplication or CMult
   * - IValue does not occur below CMult or Multiplication
   * - Multiplication does not occur below Multiplication
   * - any sub-expression that does not contain variables, is an IValue
   * Some other things may be done, but the above properties are guaranteed.
   * 
   * Note that the existing IntegerExpression is not affected, as this is an immutable structure.
   *
   * Calling this again on an already-simplified term just returns the same expression, and takes
   * only constant time. (IntegerExpressions keep track of whether they have been simplified.)
   */
  public abstract IntegerExpression simplify();

  /** This returns whether the IntegerExpression is currently in simplified form.  */
  public final boolean isSimplified() {
    return _simplified;
  }

  /**
   * This returns an integer expression obtained from adding the given constant to the current
   * expression.  If the current IntegerExpression is in simplifed form, then so is the result.
   */
  public IntegerExpression add(int constant) {
    if (constant == 0) return this;
    return new Addition(new IValue(constant), this);
  }

  /**
   * This returns an integer expression obtained from multiplying the current one by the given
   * constant.  If the current IntegerExpression is in simplified form, then so is the result.
   */
  public IntegerExpression multiply(int constant) {
    if (constant == 0) return new IValue(0);
    if (constant == 1) return this;
    return new CMult(constant, this);
  }

  /**
   * This returns an integer expression obtained from multiplying the current one by -1.  If the
   * current IntegerExpression is in simplified form, then so is the result.
   */
  public final IntegerExpression negate() {
    return multiply(-1);
  }

  public final String toString() {
    IExpPrinter printer = new IExpPrinter();
    return printer.print(this);
  }

  public final String toSmtString() {
    StringBuilder builder = new StringBuilder();
    addToSmtString(builder);
    return builder.toString();
  }

  public final boolean equals(Object other) {
    return (other instanceof IntegerExpression) && compareTo((IntegerExpression)other) == 0;
  }
}

