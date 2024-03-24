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

public final class ConstantMultiplication extends IntegerExpression {
  private int _constant;
  private IntegerExpression _main;

  /** The constructor is hidden, since IntegerExpressions should be made through the SmtFactory. */
  ConstantMultiplication(int k, IntegerExpression e) {
    _constant = k;
    _main = e;
  }

  public int queryConstant() {
    return _constant;
  }

  public IntegerExpression queryChild() {
    return _main;
  }

  public int evaluate() {
    return _constant * _main.evaluate();
  }

  public IntegerExpression multiply(int constant) {
    int newconstant = _constant * constant;
    if (newconstant == 0) return new IValue(0);
    if (newconstant == 1) return _main;
    if (constant == 1) return this;
    return new ConstantMultiplication(newconstant, _main);
  }

  public void addToSmtString(StringBuilder builder) {
    if (_constant == -1) builder.append("(- ");
    else if (_constant < 0) builder.append("(* (- " + (-_constant) + ") ");
    else builder.append("(* " + _constant + " ");
    _main.addToSmtString(builder);
    builder.append(")");
  }

  public int compareTo(IntegerExpression other) {
    return switch (other) {
      case IValue v -> 1;
      case ConstantMultiplication cm -> {
        int c = _main.compareTo(cm.queryChild());
        if (c != 0) yield c;
        else yield _constant - cm.queryConstant();
      }
      default -> _main.compareTo(other) >= 0 ? 1 : -1;
    };
  }
}

