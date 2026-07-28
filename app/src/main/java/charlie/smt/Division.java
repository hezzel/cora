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

import java.math.BigInteger;

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
  public BigInteger evaluate(Valuation val) {
    return evaluateFor(_numerator.evaluate(val), _denominator.evaluate(val));
  }

  private static BigInteger evaluateFor(BigInteger n, BigInteger d) {
    if (d.signum() == 0) return BigInteger.ZERO; // let's just make dividing by 0 return 0
    BigInteger sign = (n.signum() >= 0 && d.signum() >= 0) || (n.signum() < 0 && d.signum() < 0)
                      ? BigInteger.ONE : BigInteger.valueOf(-1);
    BigInteger abs_n = n.abs();
    BigInteger abs_d = d.abs();
    if (n.signum() >= 0) return sign.multiply(abs_n.divide(abs_d));
    else if (abs_n.remainder(abs_d).signum() == 0) return sign.multiply(abs_n.divide(abs_d));
    else return sign.multiply(abs_n.divide(abs_d).add(BigInteger.ONE));
  }

  /**
   * Helper function for the constructor: this sets _simplified to true if the division is
   * currently presented in simplified form.
   */
  private void checkSimplified() {
    if (_numerator instanceof IValue && _denominator instanceof IValue) return;
    if (!_numerator.isSimplified() || !_denominator.isSimplified()) return;
    if (_denominator instanceof IValue k) {
      _simplified = !k.queryValue().equals(BigInteger.ONE) && k.queryValue().signum() >= 0;
    }
    else if (_denominator instanceof CMult cm) {
      _simplified = cm.queryConstant().compareTo(BigInteger.TWO) >= 0;
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
        if (k.queryValue().equals(BigInteger.ONE)) return _numerator;
        if (k.queryValue().equals(BigInteger.valueOf(-1))) return _numerator.multiply(-1); // a div -1 = -a
        if (k.queryValue().signum() < 0) { // a div -b = - (a div b)
          IntegerExpression ret = new CMult(-1, new Division(n, k.multiply(-1)));
          return ret.simplify();
        }
        return new Division(n, d);
      case CMult cm:
        if (cm.queryConstant().signum() < 0) {
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

  public int hashCode() {
    return 7 * (_numerator.hashCode() * 31 + _denominator.hashCode()) + 5;
  }
}

