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
    if (_left.equals(_right)) _simplified = false;
    else _simplified = (_left instanceof SVar || _right instanceof SVar);
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

  public Constraint simplify() {
    if (_left.equals(_right)) return new Truth();
    if (_left instanceof SValue l && _right instanceof SValue r) return new Falsehood();
    return this;
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

  /** 
   * String equalities and inequalities are the largest of all constraint in the ordering.  When
   * comparing an equality and an inequality, their components are compared; if those are the same,
   * then 0 is returned when comparing to another EqS or -1 for an UneqS; otherwise an even number.
   */
  public int compareTo(Constraint other) {
    return switch (other) {
      case UneqS uns -> {
        int c = _left.compareTo(uns.queryLeft());
        if (c == 0) c = _right.compareTo(uns.queryRight());
        if (c == 0) yield -1;
        else yield 2 * c;
      }
      case EqS eqs -> {
        int c = _left.compareTo(eqs._left);
        if (c == 0) c = _right.compareTo(eqs._right);
        yield c * 2;
      }
      default -> 1;
    };
  }

  public int hashCode() {
    return 17 * (_left.hashCode() + 31 * _right.hashCode()) + 8;
  }
}

