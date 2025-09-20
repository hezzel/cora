/**************************************************************************************************
 Copyright 2025 Cynthia Kop and Liye Guo

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.substitution;

import java.util.LinkedList;
import charlie.util.Pair;
import charlie.terms.Term;
import charlie.terms.TermFactory;
import charlie.terms.Variable;

/**
 * The goal of unification is to find the most general unifier of two terms.
 * This code implements and adapts the unification algorithm for lambda-free higher-order terms in
 * Suzan Erven, "Higher Order Non-termination: Finding Loops by Unfolding in Cora".
 */
public class Unifier {
  /** Each equation is a pair of terms to be unified. The linked list is used as a stack (LIFO). */
  private final LinkedList<Pair<Term, Term>> _equations;
  /** The partial result of the finder. */
  private final MutableSubstitution _partialMgu;

  /** The constructor is private and only accessible inside the class. */
  private Unifier() {
    _equations = new LinkedList<>();
    _partialMgu = new MutableSubstitution();;
  }

  /**
   * Performs Variable Elimination by replacing x by t in every remaining equations.
   * @return false if x occurs in t, and true otherwise.
   */
  private boolean eliminateVariable(Variable x, Term t) {
    if (t.vars().contains(x)) return false;
    MutableSubstitution sub = new MutableSubstitution(x, t);
    /* Update remaining equations. */
    for (var iter = _equations.listIterator(); iter.hasNext(); ) {
      Pair<Term,Term> equ = iter.next();
      iter.set(new Pair<Term,Term>(sub.substitute(equ.fst()), sub.substitute(equ.snd())));
    }
    /* Update the partial result. */
    for (var y : _partialMgu.domain()) {
      _partialMgu.replace(y, sub.substitute(_partialMgu.get(y)));
    }
    _partialMgu.extend(x, t);
    return true;
  }

  /**
   * Performs Term Reduction by splitting up applications on both sides and requiring that if
   * l = a l1 ... ln and r = b r1 ... rn, then a = b, l1 = r1, ..., ln = rn by adding those
   * equalities to _equations.  Note that this also works if a or b is an application (but not
   * both).
   * @param l and r must be applications.
   */
  private void reduceTerm(Term l, Term r) {
    int i = l.numberArguments();
    int j = r.numberArguments();
    while (i > 0 && j > 0) {
      _equations.push(new Pair<Term,Term>(l.queryArgument(i--), r.queryArgument(j--)));
    }
    _equations.push(new Pair<Term,Term>(l.queryImmediateHeadSubterm(i),
                                        r.queryImmediateHeadSubterm(j)));
  }

  /**
   * Performs one unification step.
   * @return true if we succeeded, false if l and r are definitely not unifiable.
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
  public static MutableSubstitution mgu(Term t1, Term t2) {
    if (!t1.isApplicative() || !t2.isApplicative()) {
      throw new IllegalArgumentException("Currently unable to unify inapplicative terms.");
    }
    Unifier unifier = new Unifier();
    unifier._equations.push(new Pair<>(t1, t2));
    while (!unifier._equations.isEmpty()) {
      var equ = unifier._equations.pop();
      Term l = equ.fst();
      Term r = equ.snd();
      if (!l.queryType().equals(r.queryType()) || !unifier.unify(l, r)) {
        return null;
      }
    }
    return unifier._partialMgu;
  }
}

