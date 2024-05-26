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

import charlie.exceptions.SmtEvaluationException;

/** This class holds the negation of a boolean variable. */
public final class NBVar extends Constraint {
  private BVar _negated;

  NBVar(BVar x) {
    _negated = x;
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
    if (val == null) throw new SmtEvaluationException("!" + _negated.queryName());
    else return !val.queryBoolAssignment(_negated.queryIndex());
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("(not ");
    _negated.addToSmtString(builder);
    builder.append(")");
  }

  public boolean equals(Constraint other) {
    return (other instanceof NBVar n) && (_negated.queryIndex() == n.queryIndex());
  }
}

