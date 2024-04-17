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

import java.util.ArrayList;
import java.util.Map;
import charlie.types.Type;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.theorytranslation.TermAnalyser;
import cora.config.Settings;

/**
 * Rules are the core objects that define the reduction relation in a term rewriting system.  These
 * can be first-order or higher-order, constrained or unconstrained.  They always have the form
 * l → r : φ, although this is viewed as just l → r if there is no constraint.
 * This object reduces a term using a fixed Rule.
 */
class RuleReducer implements ReduceObject {
  private Rule _rule;

  public RuleReducer(Rule rule) {
    _rule = rule;
  }

  /**
   * If left * X1 *** Xk has the same type as t, then this function returns k; if no such k exists
   * -1 is returned instead . */
  private int findHeadAdditions(Term t) {
    Type mytype = _rule.queryType();
    Type histype = t.queryType();
    int k = 0;
    for (; mytype.isArrowType() && !mytype.equals(histype); k++) mytype = mytype.subtype(2);
    if (mytype.equals(histype)) return k;
    return -1;
  }

  /** This returns whether our rule can be applied to t at the head. */
  public boolean applicable(Term t) {
    int n = t.numberArguments();
    int k = findHeadAdditions(t);
    if (k == -1 || n < k) return false;
    Term head = t.queryImmediateHeadSubterm(n-k);
    Substitution subst = _rule.queryLeftSide().match(head);
    if (subst == null) return false;
    for (Variable x : _rule.queryConstraint().vars()) {
      if (subst.get(x) != null && !subst.get(x).isValue()) return false;
    }
    Term csub = _rule.queryConstraint().substitute(subst);
    if (csub.isGround()) return TermAnalyser.evaluate(csub).getBool();
    else return TermAnalyser.satisfy(csub, Settings.smtSolver) instanceof TermAnalyser.Result.YES;
  }

  /**
   * If the current rule can be applied to t at the head, this returns the result of a head-most
   * reduction; otherwise it returns null.
   */
  public Term apply(Term t) {
    int n = t.numberArguments();
    int k = findHeadAdditions(t);
    if (k == -1 || n < k) return null;
    Term head = t.queryImmediateHeadSubterm(n-k);
    Substitution subst = _rule.queryLeftSide().match(head);
    if (subst == null) return null;

    // check the constraint and rhs variables
    for (Variable x : _rule.queryConstraint().vars()) {
      if (subst.get(x) != null && !subst.get(x).isValue()) return null;
    }
    Term csub = _rule.queryConstraint().substitute(subst);
    if (csub.isGround()) {
      if (!TermAnalyser.evaluate(csub).getBool()) return null;
    }
    else {
      Substitution result = null;
      switch (TermAnalyser.satisfy(csub, Settings.smtSolver)) {
        case TermAnalyser.Result.NO(): return null;
        case TermAnalyser.Result.MAYBE(String reason): return null;
        case TermAnalyser.Result.YES(Substitution gamma): result = gamma;
      };
      for (Variable x : csub.vars()) {
        if (!subst.extend(x, result.get(x))) return null;
      }
    }
    for (Variable x : _rule.queryRightSide().vars()) {
      if (subst.get(x) == null) subst.extend(x, TermAnalyser.chooseRandomValue(x.queryType()));
    }

    ArrayList<Term> args = new ArrayList<Term>();
    for (int i = n-k+1; i <= n; i++) args.add(t.queryArgument(i));
    Term righthead = _rule.queryRightSide().substitute(subst);
    return righthead.apply(args);
  }

  public String toString() {
    return _rule.toString();
  }
}
