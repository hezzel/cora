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
import java.util.LinkedList;
import java.util.TreeMap;
import java.util.Collections;
import java.util.stream.Collectors;

import charlie.util.Pair;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.FunctionSymbol;
import charlie.terms.position.Position;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.trs.TRS.RuleScheme;
import cora.config.Settings;

/** A Reducer is a straightforward class to reduce terms for a given TRS. */
public class Reducer {
  private ArrayList<ReduceObject> _components;
  private TreeMap<FunctionSymbol,Integer> _arity;

  public Reducer(TRS trs) {
    _components = new ArrayList<ReduceObject>();
    _arity = new TreeMap<FunctionSymbol,Integer>();
    for (int i = 0; i < trs.querySchemeCount(); i++) {
      switch (trs.queryScheme(i)) {
        case RuleScheme.Eta: _components.add(new EtaReducer()); break;
        case RuleScheme.Beta: _components.add(new BetaReducer()); break;
        case RuleScheme.Calc: _components.add(new CalcReducer()); break;
      }
    }
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      Rule rule = trs.queryRule(i);
      _components.add(new RuleReducer(rule));
      if (!rule.queryLeftSide().isFunctionalTerm()) { _arity = null; break; }
      FunctionSymbol f = rule.queryLeftSide().queryRoot();
      int k = rule.queryLeftSide().numberArguments();
      if (!_arity.containsKey(f) || _arity.get(f) > k) _arity.put(f, k);
    }
  }

  /**
   * Returns the leftmost, innermost position where a rule or scheme may be applied, or null if no
   * such position exists.
   */
  public Position leftmostInnermostRedexPosition(Term s) {
    Pair<Term,Position> p = s.findSubterm((sub,pos) -> {
      for (int j = 0; j < _components.size(); j++) {
        if (_components.get(j).applicable(sub)) return true;
      }
      return false;
    });
    if (p == null) return null;
    return p.snd();
  }

  /** This returns true if FV(t) contains a binder variable. */
  private boolean hasBinder(Term t) {
    for (Variable x : t.vars()) {
      if (x.isBinderVariable()) return true;
    }
    return false;
  }

  /**
   * This function checks if the given term may be reduced at the root using call-by-value
   * reduction.  This is the case if:
   * - this term does not freely contain any binder variables (in CBV reduction we may never
   *   reduce between a term and its binder)
   * - all its strict subterms either are variables, are abstractions, freely contain a binder
   *   variable, or have a form f(s1,...,sn) where f is a constructor or n < arity(f)
   */
  private boolean cbvReductionOK(Term t) {
    if (hasBinder(t)) return false;
    if (_arity == null) return true;    // call-by-value is not well-defined in this TRS!

    LinkedList<Term> parts = new LinkedList<Term>();
    for (int i = 1; i <= t.numberArguments(); i++) parts.add(t.queryArgument(i));

    while (!parts.isEmpty()) {
      Term sub = parts.pop();
      if (sub.isVariable() || sub.isValue()) continue;
      for (int i = 1; i <= sub.numberArguments(); i++) parts.add(sub.queryArgument(i));
      if (sub.isAbstraction() || hasBinder(sub)) continue;
      if (!sub.isFunctionalTerm()) return false;
      FunctionSymbol root = sub.queryRoot();
      if (root.isTheorySymbol()) {
        if (!root.queryType().isArrowType()) return false;
      }
      else if (_arity.containsKey(root)) {
        if (sub.numberArguments() >= _arity.get(root)) return false;
      }
    }
    return true;
  }

  /**
   * Reduces the given term at some position in line with the strategy, and returns the result;
   * if there is no redex position, null is returned instead.
   * If multiple rules or schemes can be used, an arbitrary one is chosen.
   */
  public Term reduce(Term s) {
    // shuffle the list of all rules and rule schemes to get some randomness
    Collections.shuffle(_components);
    // handle the strategy by deciding on the (order of the) list of positions
    List<Pair<Term,Position>> subterms = s.querySubterms();
    switch (Settings.queryRewritingStrategy()) {
      case Settings.Strategy.Full:
        // for full rewriting, any redex is valid, so we just consider a random order
        Collections.shuffle(subterms);
        break;
      case Settings.Strategy.CallByValue:
        // for call-by-value rewriting, the strict subterms of the redex must be term values
        subterms =
          subterms.stream().filter(p -> cbvReductionOK(p.fst())).collect(Collectors.toList());
        break;
      case Settings.Strategy.Innermost:
        // we do nothing: the list is already ordered in (leftmost) innermost order
    }
    // go over all the subterms and all the rules, and find the first matching one!
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
      s = reduce(s);
    } while (s != null);
    return new Reduction(steps);
  }
}
