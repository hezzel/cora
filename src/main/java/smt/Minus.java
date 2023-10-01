/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.smt;

public class Minus extends IntegerExpression {
  private IntegerExpression _negated;

  /** The constructor is hidden, since IntegerExpressions should be made through the SmtFactory. */
  Minus(IntegerExpression e) {
    _negated = e;
  }

  public IntegerExpression queryChild() {
    return _negated;
  }

  public int evaluate() {
    return -(_negated.evaluate());
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("(- ");
    _negated.addToSmtString(builder);
    builder.append(")");
  }

  public boolean equals(IntegerExpression other) {
    return (other instanceof Minus) && (_negated.equals(((Minus)other).queryChild()));
  }
}

