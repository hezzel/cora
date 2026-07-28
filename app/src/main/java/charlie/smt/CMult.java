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

import java.math.BigInteger;

/** A multiplication by a constant */
public final class CMult extends IntegerExpression {
  private BigInteger _constant;
  private IntegerExpression _main;

  /** The constructor is hidden, since IntegerExpressions should be made through the SmtFactory. */
  CMult(BigInteger k, IntegerExpression e) {
    _constant = k;
    _main = e;
    if (_main.isSimplified() && !(_main instanceof IValue) &&
        !(_main instanceof CMult) && !(_main instanceof Addition) &&
        _constant.signum() != 0 && !_constant.equals(BigInteger.ONE)) _simplified = true;
  }

  /** Convenience constructor for a small (Java int) constant. */
  CMult(int k, IntegerExpression e) {
    this(BigInteger.valueOf(k), e);
  }

  public BigInteger queryConstant() {
    return _constant;
  }

  public IntegerExpression queryChild() {
    return _main;
  }

  public BigInteger evaluate(Valuation val) {
    return _constant.multiply(_main.evaluate(val));
  }

  public IntegerExpression simplify() {
    if (_simplified) return this;
    if (_constant.signum() == 0) return new IValue(BigInteger.ZERO);
    if (_constant.equals(BigInteger.ONE)) return _main.simplify();
    return _main.simplify().multiply(_constant);
  }

  public IntegerExpression multiply(BigInteger constant) {
    BigInteger newconstant = _constant.multiply(constant);
    if (newconstant.signum() == 0) return new IValue(BigInteger.ZERO);
    if (newconstant.equals(BigInteger.ONE)) return _main;
    if (constant.equals(BigInteger.ONE)) return this;
    return new CMult(newconstant, _main);
  }

  public void addToSmtString(StringBuilder builder) {
    if (_constant.equals(BigInteger.valueOf(-1))) builder.append("(- ");
    else if (_constant.signum() < 0) builder.append("(* (- " + _constant.negate() + ") ");
    else builder.append("(* " + _constant + " ");
    _main.addToSmtString(builder);
    builder.append(")");
  }

  public int compareTo(IntegerExpression other) {
    return switch (other) {
      case IValue v -> 1;
      case CMult cm -> {
        int c = _main.compareTo(cm.queryChild());
        if (c != 0) yield c;
        else yield _constant.compareTo(cm.queryConstant());
      }
      default -> _main.compareTo(other) >= 0 ? 1 : -1;
    };
  }

  public int hashCode() {
    return 2 + 7 * (_main.hashCode() * 5 + _constant.hashCode());
  }
}

