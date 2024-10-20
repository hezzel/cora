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

import charlie.exceptions.SmtEvaluationException;

public final class IVar extends IntegerExpression {
  private int _index;
  private String _name;

  /** The constructors are hidden, since IntegerExpressions should be made through an SmtProblem. */
  IVar(int i) {
    _index = i;
    _name = "i" + _index;
    _simplified = true;
  }

  /** The constructors are hidden, since IntegerExpressions should be made through an SmtProblem. */
  IVar(int i, String name) {
    _index = i;
    _name = "[" + name + "]";
    _simplified = true;
  }

  public int queryIndex() {
    return _index;
  }

  public String queryName() {
    return _name;
  }

  public int evaluate(Valuation val) {
    if (val == null) throw new SmtEvaluationException("i" + _index + " (" + _name + ")");
    else return val.queryIntAssignment(_index);
  }

  public IntegerExpression simplify() {
    return this;
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("i" + _index);
  }

  public int compareTo(IntegerExpression other) {
    return switch (other) {
      case IValue v -> 1;
      case IVar x -> _index  - x.queryIndex();
      case CMult cm -> compareTo(cm.queryChild()) <= 0 ? -1 : 1;
      case Addition a -> -1;
      case Multiplication m -> -1;
      case Division d -> -1;
      case Modulo m -> -1;
    };
  }

  public int hashCode() {
    return 7 * _index + 1;
  }
}

