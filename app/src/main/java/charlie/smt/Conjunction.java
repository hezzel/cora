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
import java.util.Collections;
import java.util.TreeSet;

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

  public Constraint negate() {
    ArrayList<Constraint> arr = new ArrayList<Constraint>();
    for (Constraint c : _children) arr.add(c.negate());
    if (_simplified) return (new Disjunction(arr)).simplify();
    return new Disjunction(arr);
  }

  public Constraint simplify() {
    if (_simplified) return this;
    // store the simplified children into a set so they're automatically ordered, and duplicates
    // are removed
    TreeSet<Constraint> set = new TreeSet<Constraint>();
    for (Constraint c : _children) {
      Constraint child = c.simplify();
      if (child instanceof Falsehood) return child;
      if (child instanceof Truth) continue;
      if (child instanceof Conjunction conj) { for (Constraint cc : conj._children) set.add(cc); }
      else set.add(child);
    }
    // build up the list from the set, but note contradictions on subsequent elements, and avoid
    // adding implied comparisons
    ArrayList<Constraint> a = new ArrayList<Constraint>(set.size());
    boolean reorder = false;
    for (Constraint c : set) {
      a.add(c);
      if (a.size() == 1) continue;
      Constraint prev = a.get(a.size()-2);
      // x ∧ !x cannot hold
      if (prev instanceof BVar x && c instanceof NBVar y &&
          x.queryIndex() == y.queryIndex()) return new Falsehood();
      // a = b and a # b cannot hold
      if (prev instanceof EqS && c instanceof UneqS &&
          prev.compareTo(c) == -1) return new Falsehood();
      // a = 0 ∧ a # 0 cannot hold
      if (prev instanceof Is0 i && c instanceof Neq0 n &&
          i.queryExpression().equals(n.queryExpression())) return new Falsehood();
      // a = 0 ∧ a ≥ 0 just means a = 0
      if (prev instanceof Is0 i && c instanceof Geq0 g &&
          i.queryExpression().equals(g.queryExpression())) a.remove(a.size()-1);
      // a ≥ 0 ∧ a # 0 just means a > 0, so a - 1 ≥ 0
      if (prev instanceof Geq0 g && c instanceof Neq0 n &&
          g.queryExpression().equals(n.queryExpression())) {
        a.remove(a.size()-1);
        a.remove(a.size()-1);
        a.add(new Geq0(g.queryExpression().add(-1)));
        reorder = true;
      }
    }
    if (a.size() == 0) return new Truth();
    if (a.size() == 1) return a.get(0);
    if (reorder) return (new Conjunction(a)).simplify();
    else return new Conjunction(a);
  }

  public int hashCode() {
    return 17 * _children.hashCode() + 2;
  }
}

