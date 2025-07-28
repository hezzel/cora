/**************************************************************************************************
 Copyright 2023--2025 Cynthia Kop

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

public final class SVar extends StringExpression {
  private int _index;
  private String _name;

  /** The constructors are hidden, since StringExpressions should be made through an SmtProblem. */
  SVar(int i) {
    _index = i;
    _name = "s" + _index;
  }

  /** The constructors are hidden, since StringExpressions should be made through an SmtProblem. */
  SVar(int i, String name) {
    _index = i;
    _name = "[" + name + "]";
  }

  public int queryIndex() {
    return _index;
  }

  public String queryName() {
    return _name;
  }

  public String evaluate(Valuation val) {
    if (val == null) throw new SmtEvaluationException(this);
    else return val.queryStringAssignment(_index);
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("s" + _index);
  }

  public int compareTo(StringExpression other) {
    return switch (other) {
      case SValue v -> 1;
      case SVar x -> _index  - x.queryIndex();
    };
  }

  public int hashCode() {
    return 2 * _index + 1;
  }
}

