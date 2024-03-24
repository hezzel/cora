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

/** Not a public class on purpose: use Constraint, or use Greater/Geq directly. */
abstract sealed class Comparison extends Constraint
    permits Greater, Geq, Equal, Distinct {

  protected IntegerExpression _left;
  protected IntegerExpression _right;

  protected abstract boolean evaluate(int l, int r);
  protected abstract String symbol();

  protected Comparison(IntegerExpression left, IntegerExpression right) {
    _left = left;
    _right = right;
  }

  public IntegerExpression queryLeft() { return _left; }
  public IntegerExpression queryRight() { return _right; }

  public boolean evaluate() {
    int x = _left.evaluate();
    int y = _right.evaluate();
    return evaluate(x, y);
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("(");
    builder.append(symbol());
    builder.append(" ");
    _left.addToSmtString(builder);
    builder.append(" ");
    _right.addToSmtString(builder);
    builder.append(")");
  }

  public boolean equals(Constraint other) {
    if (!(other instanceof Comparison)) return false;
    Comparison c = (Comparison)other;
    return c.symbol().equals(symbol()) &&
      _left.equals(c.queryLeft()) && _right.equals(c.queryRight());
  }
}

