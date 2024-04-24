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

public final class Modulo extends IntegerExpression {
  private IntegerExpression _numerator;
  private IntegerExpression _denominator;

  /** The constructor is hidden, since IntegerExpressions should be made through the SmtFactory. */
  Modulo(IntegerExpression n, IntegerExpression d) {
    _numerator = n;
    _denominator = d;
    checkSimplified();
  }

  public IntegerExpression queryNumerator() {
    return _numerator;
  }

  public IntegerExpression queryDenominator() {
    return _denominator;
  }

  /**
   * Returns the unique value m between 0 and abs(_denominator)-1 such that
   * _numerator = _denominator * r + m for some r; that is: a % b following the SMTLIB standard
   * (this is *not* the same as what _numerator % _denominator returns in Java when negative
   * values are concerned).
   */
  public int evaluate(Valuation val) {
    return evaluateFor(_numerator.evaluate(val), _denominator.evaluate(val));
  }

  private static int evaluateFor(int n, int d) {
    if (d == 0) return 0; // let's just make dividing by 0 return 0
    int abs_n = n >= 0 ? n : - n;
    int abs_d = d >= 0 ? d : - d;
    int ret = abs_n % abs_d;
    if (n >= 0 || ret == 0) return ret;
    return abs_d - ret;
  }

  /**
   * Helper function for the constructor: this sets _simplified to true if the division is
   * currently presented in simplified form.
   */
  private void checkSimplified() {
    if (_numerator instanceof IValue && _denominator instanceof IValue) return;
    if (!_numerator.isSimplified() || !_denominator.isSimplified()) return;
    if (_denominator instanceof IValue k) {
      _simplified = k.queryValue() != 1 && k.queryValue() >= 0;
    }
    else if (_denominator instanceof CMult cm) {
      _simplified = cm.queryConstant() >= 2;
    }
    else _simplified = true;
  }

  public IntegerExpression simplify() {
    if (_simplified) return this;
    IntegerExpression n = _numerator.simplify();
    IntegerExpression d = _denominator.simplify();
    switch (_denominator) {
      case IValue k:
        if (n instanceof IValue i) return new IValue(evaluateFor(i.queryValue(), k.queryValue()));
        if (k.queryValue() == 1 || k.queryValue() == -1) return new IValue(0);
        if (k.queryValue() < 0) { // a mod -b = a mod b
          return new Modulo(n, k.multiply(-1));
        }
        return new Modulo(n, d);
      case CMult cm:
        if (cm.queryConstant() < 0) {
          return new Modulo(n, cm.multiply(-1));
        }
      default:
        return new Modulo(n, d);
    }
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("(mod ");
    _numerator.addToSmtString(builder);
    builder.append(" ");
    _denominator.addToSmtString(builder);
    builder.append(")");
  }

  public int compareTo(IntegerExpression other) {
    return switch (other) {
      case IValue v -> 1;
      case IVar x -> 1;
      case CMult cm -> compareTo(cm.queryChild()) <= 0 ? -1 : 1;
      case Addition a -> 1;
      case Multiplication m -> 1;
      case Division m -> 1;
      case Modulo m -> {
        int c = _denominator.compareTo(m._denominator);
        if (c != 0) yield c;
        else yield _numerator.compareTo(m._numerator);
      }   
    };
  }
}

