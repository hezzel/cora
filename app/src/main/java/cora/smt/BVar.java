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

import cora.exceptions.SmtEvaluationError;

public class BVar extends Constraint {
  private int _index;

  /** The constructor is hidden, since Constraints should be made through the SmtFactory. */
  BVar(int i) {
    _index = i;
  }

  public int queryIndex() {
    return _index;
  }

  public boolean evaluate() {
    throw new SmtEvaluationError("b" + _index);
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("b" + _index);
  }

  public boolean equals(Constraint other) {
    return (other instanceof BVar) && (_index == ((BVar)other).queryIndex());
  }
}

