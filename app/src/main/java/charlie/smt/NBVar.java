/**************************************************************************************************
 Copyright 2024--2025 Cynthia Kop

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

/** This class holds the negation of a boolean variable. */
public final class NBVar extends Constraint {
  private BVar _negated;

  NBVar(BVar x) {
    _negated = x;
    _simplified = true;
  }

  public int queryIndex() {
    return _negated.queryIndex();
  }

  public String queryName() {
    return _negated.queryName();
  }

  public BVar negate() {
    return _negated;
  }

  public boolean evaluate(Valuation val) {
    if (val == null) throw new SmtEvaluationException(_negated);
    else return !val.queryBoolAssignment(_negated.queryIndex());
  }

  public NBVar simplify() {
    return this;
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("(not ");
    _negated.addToSmtString(builder);
    builder.append(")");
  }

  public int compareTo(Constraint other) {
    return switch (other) {
      case Falsehood f -> 1;
      case Truth t -> 1;
      case NBVar x -> _negated.queryIndex() - x.queryIndex();
      case BVar x -> {
        int ret = _negated.queryIndex() - x.queryIndex();
        if (ret == 0) yield 1;
        else yield ret;
      }
      default -> -1;
    };
  }

  public int hashCode() { return _negated.hashCode() + 1; }
}

