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

public final class BVar extends Constraint {
  private int _index;
  private String _name;

  /** The constructors are hidden, since Constraints should be made through the SmtFactory. */
  BVar(int i) {
    _index = i;
    _name = "b" + _index;
    _simplified = true;
  }

  BVar(int i, String name) {
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

  public NBVar negate() {
    return new NBVar(this);
  }

  public boolean evaluate(Valuation val) {
    if (val == null) throw new SmtEvaluationException(this);
    else return val.queryBoolAssignment(_index);
  }

  public BVar simplify() {
    return this;
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("b" + _index);
  }

  public int compareTo(Constraint other) {
    return switch (other) {
      case Falsehood _ -> 1;
      case Truth _ -> 1;
      case BVar x -> _index - x._index;
      case NBVar x -> {
        int ret = _index - x.queryIndex();
        if (ret == 0) yield -1;
        else yield ret;
      }
      default -> -1; 
    };
  }

  public int hashCode() {
    return 17 * _index;
  }
}

