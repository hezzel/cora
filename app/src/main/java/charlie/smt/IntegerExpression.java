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
  permits IVar, IValue, Division, Modulo, ConstantMultiplication, Multiplication, Addition {
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
   * This returns an integer expression obtained from multiplying the current one by the given
   * constant.  If the current IntegerExpression is in simplified form, then so is the result.
   */
  public IntegerExpression multiply(int constant) {
    if (constant == 0) return new IValue(0);
    if (constant == 1) return this;
    return new ConstantMultiplication(constant, this);
  }

  /**
   * This returns an integer expression obtained from multiplying the current one by -1.  If the
   * current IntegerExpression is in simplified form, then so is the result.
   */
  public final IntegerExpression negate() {
    return multiply(-1);
  }

  public final String toString() {
    StringBuilder builder = new StringBuilder();
    addToSmtString(builder);
    return builder.toString();
  }

  public final boolean equals(Object other) {
    return (other instanceof IntegerExpression) && compareTo((IntegerExpression)other) == 0;
  }
}

