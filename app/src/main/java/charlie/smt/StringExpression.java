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

package charlie.smt;

import java.lang.Comparable;

/**
 * A StringExpression is currently either a string value or a variable.  In the future it may be
 * extended to for instance support concatenation.  We mostly support this to allow I/O through
 * reduction.an expression built from integer values, addition, multiplication, etc.:
 * the symbols in the integer theory, yielding an int.
 */

public sealed abstract class StringExpression implements Comparable<StringExpression>
  permits SVar, SValue {

  /**
   * This evaluates the current expression, taking the values for all variables from the given
   * valuation.
   */
  public abstract String evaluate(Valuation val);

  /** Adds the SMT description of the current expression to the given string builder. */
  public abstract void addToSmtString(StringBuilder builder);

  /**
   * This generates a total ordering on string expressions.  Constants are guaranteed to be minimal
   * in the ordering (compared to expressions that are not constants).
   */
  public abstract int compareTo(StringExpression other);

  /**
   * Assuming the current expression has no variables, this function evaluates it to its string
   * value.  If there is a variable in it, an SmtEvaluationException will be thrown instead.
   */
  public final String evaluate() { return evaluate(null); }

  public final String toString() {
    SExpPrinter printer = new SExpPrinter();
    return printer.print(this);
  }

  public final String toSmtString() {
    StringBuilder builder = new StringBuilder();
    addToSmtString(builder);
    return builder.toString();
  }

  public final boolean equals(Object other) {
    return (other instanceof StringExpression) && compareTo((StringExpression)other) == 0;
  }
}

