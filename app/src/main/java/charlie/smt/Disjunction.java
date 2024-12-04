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
import java.util.TreeSet;

public final class Disjunction extends Junction {
  Disjunction(Constraint a, Constraint b) {
    super(a, b);
  }

  Disjunction(List<Constraint> args) {
    super(args);
  }

  protected String symbol() { return "or"; }

  public boolean evaluate(Valuation val) {
    for (int i = 0; i < _children.size(); i++) {
      if (_children.get(i).evaluate(val)) return true;
    }
    return false;
  }

  public Constraint negate() {
    ArrayList<Constraint> arr = new ArrayList<Constraint>();
    for (Constraint c : _children) arr.add(c.negate());
    if (_simplified) return (new Conjunction(arr)).simplify();
    return new Conjunction(arr);
  }

  public Constraint simplify() {
    if (_simplified) return this;
    // store the simplified children into a set so they're automatically ordered, and duplicates
    // are removed
    TreeSet<Constraint> set = new TreeSet<Constraint>();
    for (Constraint c : _children) {
      Constraint child = c.simplify();
      if (child instanceof Falsehood) continue;
      if (child instanceof Truth) return child;
      if (child instanceof Disjunction disj) { for (Constraint cc : disj._children) set.add(cc); }
      else set.add(child);
    }
    // build up the list from the set, but note elements that combine to T or imply each other
    ArrayList<Constraint> a = new ArrayList<Constraint>(set.size());
    for (Constraint c : set) {
      if (a.size() == 0) { a.add(c); continue; }
      Constraint prev = a.get(a.size()-1);
      // x ∨ !x is always true
      if (prev instanceof BVar x && c instanceof NBVar y &&
          x.queryIndex() == y.queryIndex()) return new Truth();
      // a = b ∨ a # b is always true
      if (prev instanceof EqS && c instanceof UneqS &&
          prev.compareTo(c) == -1) return new Truth();
      // a = 0 ∨ a # 0 is always true, as is a ≥ 0 ∨ a # 0
      if (c instanceof Neq0 n) {
        if ( (prev instanceof Is0 i && i.queryExpression().equals(n.queryExpression())) ||
             (prev instanceof Geq0 g && g.queryExpression().equals(n.queryExpression())) ) {
          return new Truth();
        }
      }
      // a = 0 ∨ a ≥ 0 just means a ≥ 0
      if (prev instanceof Is0 i && c instanceof Geq0 g &&
          i.queryExpression().equals(g.queryExpression())) a.set(a.size()-1, c);
      else a.add(c);
    }
    if (a.size() == 0) return new Falsehood();
    if (a.size() == 1) return a.get(0);
    return new Disjunction(a);
  }

  public int hashCode() {
    return 17 * _children.hashCode() + 3;
  }
}

