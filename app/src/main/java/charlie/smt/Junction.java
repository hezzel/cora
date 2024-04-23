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

import java.util.ArrayList;
import java.util.List;
import charlie.exceptions.IndexingError;

/** Shared inherit functionality for Conjunction and Disjunction; do not use on its own. */
abstract sealed class Junction extends Constraint permits Conjunction, Disjunction {
  protected ArrayList<Constraint> _children;

  protected abstract String symbol();

  Junction(Constraint a, Constraint b) {
    _children = new ArrayList<Constraint>();
    addChild(a);
    addChild(b);
  }

  Junction(List<Constraint> args) {
    _children = new ArrayList<Constraint>();
    for (int i = 0; i < args.size(); i++) addChild(args.get(i));
  }

  private void addChild(Constraint child) {
    if (child instanceof Junction j && j.symbol().equals(symbol())) {
      for (int i = 1; i <= j.numChildren(); i++) _children.add(j.queryChild(i));
    }
    else _children.add(child);
  }

  public int numChildren() {
    return _children.size();
  }

  public Constraint queryChild(int index) {
    if (index <= 0 || index > _children.size()) {
      throw new IndexingError("Junction", "queryChild", index, 1, _children.size());
    }
    return _children.get(index-1);
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("(");
    builder.append(symbol());
    for (int i = 0; i < _children.size(); i++) {
      builder.append(" ");
      _children.get(i).addToSmtString(builder);
    }
    builder.append(")");
  }

  public boolean equals(Constraint other) {
    if (!(other instanceof Junction)) return false;
    Junction j = (Junction)other;
    if (!symbol().equals(j.symbol())) return false;
    if (j.numChildren() != _children.size()) return false;
    for (int i = 0; i < _children.size(); i++) {
      if (!_children.get(i).equals(j.queryChild(i+1))) return false;
    }
    return true;
  }
}

