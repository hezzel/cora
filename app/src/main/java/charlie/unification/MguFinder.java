/**************************************************************************************************
 Copyright 2025 Cynthia Kop & Liye Guo

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.unification;

import java.util.LinkedList;
import charlie.util.Pair;
import charlie.terms.Term;
import charlie.terms.TermFactory;
import charlie.terms.Variable;
import charlie.terms.Substitution;

/**
 * Finds the most general unifier (MGU) of two terms.
 * Implements the unification algorithm in
 * Suzan Erven, "Higher Order Non-termination: Finding Loops by Unfolding in Cora".
 */
public class MguFinder {
  /**
   * Each equation is a pair of terms to be unified.
   * The linked list is used as a stack (LIFO).
   */
  private final LinkedList<Pair<Term, Term>> _equations =
    new LinkedList<>();
  /**
   * The partial result of the finder.
   */
  private final Substitution _partialMgu =
    TermFactory.createEmptySubstitution();

  /**
   * The constructor is private and only accessible inside the class.
   */
  private MguFinder() {}

  /**
   * Performs Variable Elimination.
   * @return false if x occurs in t, and true otherwise.
   */
  private boolean eliminateVariable(Variable x, Term t) {
    if (t.vars().contains(x)) return false;
    Substitution sub = TermFactory.createEmptySubstitution();
    sub.extend(x, t);
    /* Update remaining equations. */
    for (var iter = _equations.listIterator();
         iter.hasNext();) {
      var equ = iter.next();
      iter.set(new Pair<>(
        equ.fst().substitute(sub),
        equ.snd().substitute(sub)));
    }
    /* Update the partial result. */
    for (var y : _partialMgu.domain()) {
      _partialMgu.replace(y, _partialMgu.get(y).substitute(sub));
    }
    _partialMgu.extend(x, t);
    return true;
  }

  /**
   * Performs Term Reduction.
   * @param l and r must be applications.
   */
  private void reduceTerm(Term l, Term r) {
    int i = l.numberArguments();
    int j = r.numberArguments();
    while (i > 0 && j > 0) {
      _equations.push(new Pair<>(
        l.queryArgument(i--),
        r.queryArgument(j--)));
    }
    _equations.push(new Pair<>(
      l.queryImmediateHeadSubterm(i),
      r.queryImmediateHeadSubterm(j)));
  }

  /**
   * Performs one unification step.
   * @return whether l and r are unifiable.
   */
  private boolean unify(Term l, Term r) {
    if (l.isVariable() || r.isVariable()) {
      if (l.equals(r)) return true;
      return l.isVariable() ?
        eliminateVariable(l.queryVariable(), r) :
        eliminateVariable(r.queryVariable(), l);
    }
    if (l.isApplication() && r.isApplication()) {
      reduceTerm(l, r);
      return true;
    }
    /* At this point, neither term is a variable and at least one is not an application.
     * Therefore, (at least) one is a constant, and the other is not a variable.
     */
    return l.equals(r);
  }

  /**
   * The method for unification, publicly accessible.
   * @return an MGU of t1 and t2 if unifiable, and null otherwise.
   */
  public static Substitution mgu(Term t1, Term t2) {
    if (!t1.isApplicative() || !t2.isApplicative()) {
      throw new IllegalArgumentException("Currently unable to unify inapplicative terms.");
    }
    MguFinder finder = new MguFinder();
    finder._equations.push(new Pair<>(t1, t2));
    while (!finder._equations.isEmpty()) {
      var equ = finder._equations.pop();
      Term l = equ.fst();
      Term r = equ.snd();
      if (!l.queryType().equals(r.queryType()) || !finder.unify(l, r)) {
        return null;
      }
    }
    return finder._partialMgu;
  }
}
