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

public final class Division extends IntegerExpression {
  private IntegerExpression _numerator;
  private IntegerExpression _denominator;

  /** The constructor is hidden, since IntegerExpressions should be made through the SmtFactory. */
  Division(IntegerExpression n, IntegerExpression d) {
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
   * Returns the unique value r such that _numerator = _denominator * r + (_numerator % _denominator);
   * that is: a / b following the SMTLIB standard (this is *not* the same as what _numerator /
   * _denominator returns in Java when negative values are concerned.
   */
  public int evaluate(Valuation val) {
    return evaluateFor(_numerator.evaluate(val), _denominator.evaluate(val));
  }

  private static int evaluateFor(int n, int d) {
    if (d == 0) return 0; // let's just make dividing by 0 return 0
    int sign = (n >= 0 && d >= 0) || (n < 0 && d < 0) ? 1 : -1;
    int abs_n = n >= 0 ? n : - n;
    int abs_d = d >= 0 ? d : - d;
    if (n >= 0) return sign * (abs_n / abs_d);
    else if (abs_n % abs_d == 0) return sign * (abs_n / abs_d);
    else return sign * (abs_n / abs_d + 1);
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
        if (k.queryValue() == 1) return _numerator;
        if (k.queryValue() == -1) return _numerator.multiply(-1); // a div -1 = -a
        if (k.queryValue() < 0) { // a div -b = - (a div b)
          IntegerExpression ret = new CMult(-1, new Division(n, k.multiply(-1)));
          return ret.simplify();
        }
        return new Division(n, d);
      case CMult cm:
        if (cm.queryConstant() < 0) {
          IntegerExpression ret = new CMult(-1, new Division(n, cm.multiply(-1)));
          return ret.simplify();
        }
      default:
        return new Division(n, d);
    }
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("(div ");
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
      case Division d -> {
        int c = _denominator.compareTo(d._denominator);
        if (c != 0) yield c;
        else yield _numerator.compareTo(d._numerator);
      }
      case Modulo m -> -1;
    };
  }
}

