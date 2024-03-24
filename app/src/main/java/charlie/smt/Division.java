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
  public int evaluate() {
    int d = _denominator.evaluate();
    if (d == 0) return 0; // let's just make dividing by 0 return 0
    int n = _numerator.evaluate();
    int sign = (n >= 0 && d >= 0) || (n < 0 && d < 0) ? 1 : -1;
    int abs_n = n >= 0 ? n : - n;
    int abs_d = d >= 0 ? d : - d;
    if (n >= 0) return sign * (abs_n / abs_d);
    else if (abs_n % abs_d == 0) return sign * (abs_n / abs_d);
    else return sign * (abs_n / abs_d + 1);
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
      case ConstantMultiplication cm -> compareTo(cm.queryChild()) <= 0 ? -1 : 1;
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

