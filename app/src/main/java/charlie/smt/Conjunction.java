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

import java.util.List;
import java.util.ArrayList;
import charlie.exceptions.IndexingError;

public final class Conjunction extends Junction {
  Conjunction(Constraint a, Constraint b) {
    super(a, b);
  }

  Conjunction(List<Constraint> args) {
    super(args);
  }

  protected String symbol() {
    return "and";
  }

  public boolean evaluate(Valuation val) {
    for (int i = 0; i < _children.size(); i++) {
      if (!_children.get(i).evaluate(val)) return false;
    }
    return true;
  }

  public Disjunction negate() {
    ArrayList<Constraint> arr = new ArrayList<Constraint>();
    for (Constraint c : _children) arr.add(c.negate());
    return new Disjunction(arr);
  }
}

