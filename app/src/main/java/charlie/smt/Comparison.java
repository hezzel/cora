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

import charlie.util.Pair;

/** Not a public class on purpose: use Constraint, or use Geq0, Is0 or Neq0 directly. */
abstract sealed class Comparison extends Constraint permits Geq0, Is0, Neq0 {
  protected IntegerExpression _expr;

  protected abstract boolean evaluate(int num);
  protected abstract String symbol();
  public abstract Comparison negate();

  protected Comparison(IntegerExpression expr) {
    _expr = expr;
  }

  /** Constructor used when comparing two numbers to each other, instead of one to 0. */
  protected Comparison(IntegerExpression left, IntegerExpression right) {
    _expr = new Addition(left, right.multiply(-1));
  }

  public IntegerExpression queryExpression() {
    return _expr;
  }

  public boolean evaluate() {
    return evaluate(_expr.evaluate());
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("(");
    builder.append(symbol());
    builder.append(" ");
    _expr.addToSmtString(builder);
    builder.append(" 0)");
  }

  public boolean equals(Constraint other) {
    if (!(other instanceof Comparison)) return false;
    Comparison c = (Comparison)other;
    return c.symbol().equals(symbol()) && _expr.equals(c.queryExpression());
  }
}

