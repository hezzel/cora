/**************************************************************************************************
 Copyright 2019--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.reduction;

import java.util.List;
import java.util.ArrayList;
import java.util.Collections;

import cora.utils.Pair;
import cora.terms.Term;
import cora.terms.position.Position;
import cora.trs.TRS;
import cora.trs.TRS.RuleScheme;

/** A Reducer is a straightforward class to reduce terms for a given TRS. */
public class Reducer {
  private ArrayList<ReduceObject> _components;

  public Reducer(TRS trs) {
    _components = new ArrayList<ReduceObject>();
    for (int i = 0; i < trs.querySchemeCount(); i++) {
      switch (trs.queryScheme(i)) {
        case RuleScheme.Eta: _components.add(new EtaReducer()); break;
        case RuleScheme.Beta: _components.add(new BetaReducer()); break;
        case RuleScheme.Calc: _components.add(new CalcReducer()); break;
        case RuleScheme.Projection: break; // TODO: implement projection
      }
    }
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      _components.add(new RuleReducer(trs.queryRule(i)));
    }
  }

  /**
   * Returns the leftmost, innermost position where a rule or scheme may be applied, or null if no
   * such position exists.
   */
  public Position leftmostInnermostRedexPosition(Term s) {
    List<Pair<Term,Position>> subterms = s.querySubterms();
    for (int i = 0; i < subterms.size(); i++) {
      Term sub = subterms.get(i).fst();
      Position pos = subterms.get(i).snd();
      for (int j = 0; j < _components.size(); j++) {
        if (_components.get(j).applicable(sub)) return pos;
      }
    }
    return null;
  }

  /**
   * Reduces the given term at the leftmost, innermost redex position, and returns the result;
   * if no such position exists, null is returned instead.
   * If multiple rules or schemes match, an arbitrary one is chosen.
   */
  public Term leftmostInnermostReduce(Term s) {
    // shuffle the list of all rules and rule schemes to get some randomness
    Collections.shuffle(_components);

    List<Pair<Term,Position>> subterms = s.querySubterms();
    for (int i = 0; i < subterms.size(); i++) {
      Term sub = subterms.get(i).fst();
      Position pos = subterms.get(i).snd();
      Term result = null;
      for (int j = 0; j < _components.size() && result == null; j++) {
        result = _components.get(j).apply(sub);
      }
      if (result != null) return s.replaceSubterm(pos, result);
    }
    return null;
  }

  public Reduction normalise(Term s) {
    ArrayList<Term> steps = new ArrayList<Term>();
    do {
      steps.add(s);
      s = leftmostInnermostReduce(s);
    } while (s != null);
    return new Reduction(steps);
  }
}
