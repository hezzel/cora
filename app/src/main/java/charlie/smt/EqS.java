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

/** This class represents equality on string expressions */
public final class EqS extends Constraint {
  private StringExpression _left;
  private StringExpression _right;

  /** Constructor is hidden, since StringExpressions should be made through the SmtFactory */
  EqS(StringExpression left, StringExpression right) {
    if (left.compareTo(right) >= 0) { _left = left; _right = right; }
    else { _left = right; _right = left; }
  }

  public StringExpression queryLeft() {
    return _left;
  }

  public StringExpression queryRight() {
    return _right;
  }

  public boolean evaluate(Valuation val) {
    return _left.evaluate(val).equals(_right.evaluate(val));
  }

  /** Returns the negation of the current constraint (an inequality) */
  public UneqS negate() {
    return new UneqS(_left, _right);
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("(= ");
    _left.addToSmtString(builder);
    builder.append(" ");
    _right.addToSmtString(builder);
    builder.append(")");
  }

  public boolean equals(Constraint other) {
    return (other instanceof EqS o) && (_left.equals(o._left)) && (_right.equals(o._right));
  }

  public int hashCode() {
    return 17 * (_left.hashCode() + 31 * _right.hashCode()) + 9;
  }
}
