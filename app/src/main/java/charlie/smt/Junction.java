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
import charlie.exceptions.IndexingException;

/** Shared inherit functionality for Conjunction and Disjunction; do not use on its own. */
abstract sealed class Junction extends Constraint permits Conjunction, Disjunction {
  protected ArrayList<Constraint> _children;

  protected abstract String symbol();

  Junction(Constraint a, Constraint b) {
    _children = new ArrayList<Constraint>();
    addChild(a);
    addChild(b);
    _simplified = checkSimplified();
  }

  Junction(List<Constraint> args) {
    _children = new ArrayList<Constraint>();
    for (Constraint c : args) addChild(c);
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
      throw new IndexingException("Junction", "queryChild", index, 1, _children.size());
    }
    return _children.get(index-1);
  }

  public boolean checkSimplified() {
    // a conjunction or disjunction should always have 2 or more elements
    if (_children.size() < 2) return false;
    // neither conjunction nor disjunction may contain a boolean constant; this in particular means
    // that the first cannot be a constant, since the ordering requirement then guarantees that the
    // rest is not a constant either
    if (_children.get(0) instanceof Truth || _children.get(0) instanceof Falsehood) return false;
    if (!_children.get(0).isSimplified()) return false;
    // the elements should be simplified, in the right order, and we cannot have both e R 0 and
    // e R' 0, nor x and !x
    for (int i = 1; i < _children.size(); i++) {
      Constraint c = _children.get(i);
      int k = _children.get(i-1).compareTo(c);
      if (!c.isSimplified()) return false;
      if (k >= 0) return false;
      if (k == -1 && c instanceof Comparison) return false;
      if (k == -1 && c instanceof NBVar n && n.negate().equals(_children.get(i-1))) return false;
    }
    return true;
  }

  public Constraint simplify() {
    return this;
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

  public int compareTo(Constraint other) {
    return switch (other) {
      case Falsehood _ -> 1;
      case Truth _ -> 1;
      case BVar _ -> 1;
      case NBVar _ -> 1;
      case Comparison _ -> 1;
      case Junction junc -> {
        int c = symbol().compareTo(junc.symbol());
        if (c == 0) c = _children.size() - junc.numChildren();
        if (c != 0) yield c;
        for (int i = 1; i <= _children.size() && c == 0; i++) {
          c = _children.get(i-1).compareTo(junc.queryChild(i));
        }
        yield c;
      }
      case Iff _ -> -1; 
      case EqS _ -> -1; 
      case UneqS _ -> -1; 
    };  
  }
}

