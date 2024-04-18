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

public final class IValue extends IntegerExpression {
  private int _k;

  /** The constructor is hidden, since IntegerExpressions should be made through the SmtFactory. */
  IValue(int i) {
    _k = i;
    _simplified = true;
  }

  public int queryValue() {
    return _k;
  }

  public int evaluate(Valuation val) {
    return _k;
  }

  public IntegerExpression simplify() {
    return this;
  }

  public IntegerExpression add(int value) {
    return new IValue(value + _k);
  }

  public IntegerExpression multiply(int value) {
    return new IValue(value * _k);
  }

  public void addToSmtString(StringBuilder builder) {
    if (_k >= 0) builder.append("" + _k);
    else builder.append("(- " + (-_k) + ")");
  }

  public int compareTo(IntegerExpression other) {
    return switch (other) {
      case IValue v -> _k - v.queryValue();
      default -> -1;
    };
  }
}

