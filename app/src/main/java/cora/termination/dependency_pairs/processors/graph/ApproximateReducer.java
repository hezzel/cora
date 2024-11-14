/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.termination.dependency_pairs.processors.graph;

import charlie.exceptions.NullStorageException;
import charlie.util.Pair;
import charlie.types.TypeFactory;
import charlie.terms.*;
import charlie.trs.TrsProperties.*;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.theorytranslation.TermAnalyser;
import cora.config.Settings;
import cora.termination.dependency_pairs.DP;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * This is a helper class exclusive to this package.  It helps in the creation of a graph
 * approximation by assessing if it is possible for an instance of one term to reduce to an
 * instance of another using the rules in the given rules set, and with term formation
 * restricted by the given TRS.
 *
 * Usage: create, call isApplicable(), and if yes call mayReduce().
 */
class ApproximateReducer {
  private TRS _coreTRS;
  private List<Rule> _rules;

  /**
   * Creates an ApproximateReducer assessment object that will use the given TRS both for term
   * formation and for reduction.
   */
  public ApproximateReducer(TRS trs) {
    if (trs == null) throw new NullStorageException("ApproximateReducer", "trs argument.");
    _coreTRS = trs;
    _rules = trs.queryRules();
  }

  /**
   * Creates an ApproximateReducer assessment object that will use the given TRS for term
   * formation and the given rules for reduction.
   */
  public ApproximateReducer(TRS trs, List<Rule> rules) {
    if (trs == null) throw new NullStorageException("ApproximateReducer", "trs argument.");
    _coreTRS = trs;
    _rules = rules;
  }

  /** If this returns false, DO NOT CALL mayReduce!  This may lead to runtimes. */
  public boolean isApplicable() {
    if (!_coreTRS.verifyProperties(Level.APPLICATIVE, Constrained.YES, TypeLevel.SIMPLE,
                                   Lhs.NONPATTERN, Root.ANY, FreshRight.CVARS)) {
      return false;
    }
    for (Rule rule : _rules) {
      if (!rule.queryLeftSide().isFunctionalTerm()) return false;
      if (!rule.queryLeftSide().isPattern()) return false;
    }
    return true;
  }

  /**
   * Creates a copy of the given dependency pairs with all variables renamed to fresh ones.
   * (The new variables will have the same printable names, but will be different for comparison
   * purposes.)
   */
  static DP rename(DP dp) {
    Substitution subst = TermFactory.createEmptySubstitution();
    for (Variable x : dp.lhs().vars()) {
      if (subst.get(x) == null) subst.extend(x, TermFactory.createVar(x.queryName(), x.queryType()));
    }
    for (Variable x : dp.rhs().vars()) {
      if (subst.get(x) == null) subst.extend(x, TermFactory.createVar(x.queryName(), x.queryType()));
    }
    for (Variable x : dp.constraint().vars()) {
      if (subst.get(x) == null) subst.extend(x, TermFactory.createVar(x.queryName(), x.queryType()));
    }
    Term newleft = dp.lhs().substitute(subst);
    Term newright = dp.rhs().substitute(subst);
    Term newconstraint = dp.constraint().substitute(subst);

    TreeSet<Variable> theory = new TreeSet<>();
    for (Variable x : dp.lvars()) {
      if (subst.get(x) != null) theory.add(subst.get(x).queryVariable());
    }
    return new DP(newleft, newright, newconstraint, theory);
  }

  /** Helper function: creates phi ∧ psi */
  private Term makeAnd(Term phi, Term psi) {
    return TheoryFactory.createConjunction(phi, psi);
  }

  /**
   * This computes, for every defined symbol, the smallest number of arguments with which f occurs
   * in some rule, on the left-hand side.  If f is not a defined symbol, it is not stored.
   * (Default rather than private for the sake of unit testing.)
   */
  TreeMap<FunctionSymbol,Integer> computeRuleArities() {
    TreeMap<FunctionSymbol,Integer> ret = new TreeMap<FunctionSymbol,Integer>();
    for (Rule rule : _rules) {
      FunctionSymbol f = rule.queryLeftSide().queryRoot();
      int k = rule.queryLeftSide().numberArguments();
      if (!ret.containsKey(f) || ret.get(f) > k) ret.put(f, k);
    }
    return ret;
  }

  /** Returns true if vars ⊆ theory */
  private boolean allVarsInTheory(Environment<Variable> vars, Set<Variable> theory) {
    for (Variable x : vars) {
      if (!theory.contains(x)) return false;
    }
    return true;
  }

  /**
   * This function returns true if there exist some substitution γ that respects dp1, and some
   * substitution δ that respects dp2, such that dp1.right reduces to dp2.left (or might** reduce).
   * It returns false if we can guarantee that it will not.
   *
   * [**] This is undecidable in general, so there are false positives, but we guarantee that there
   * are no false negatives.
   */
  public boolean mayReduce(DP dp1, DP dp2) {
    TreeMap<FunctionSymbol,Integer> ruleArity = computeRuleArities();
    
    // it's easier to use a single substitution, so make sure they have disjoint variables!
    dp2 = rename(dp2);
    // invariant: for the requirement to hold, all the pairs on the stack must be equal, and
    // requirements must be satisfiable
    Stack<Pair<Term,Term>> todo = new Stack<Pair<Term,Term>>();
    todo.push(new Pair<Term,Term>(dp1.rhs(), dp2.lhs()));
    Term requirements = makeAnd(dp1.constraint(), dp2.constraint());
    while (!todo.isEmpty()) {
      Pair<Term,Term> pair = todo.pop();
      Term from = pair.fst();
      Term to = pair.snd();

      // CASE 1: from is a base-type theory term whose variables are all instantiated by ground
      // theory terms ==> to must either be its value, or have the same either shape (in which case
      // we fall through to case 6)
      if (from.isTheoryTerm() && from.queryType().isBaseType() &&
          allVarsInTheory(from.vars(), dp1.lvars())) {
        if (!to.isTheoryTerm()) return false;
        if (to.isValue() || to.isVariable()) {
          requirements = makeAnd(requirements, TheoryFactory.createEquality(from, to));
          continue;
        }
        else {
          if (from.isValue()) return false;
          if (from.isVariable() && dp1.constraint().vars().contains(from.queryVariable())) {
            return false;
          }
        }
      }

      // CASE 2: otherwise, variables or varterms may be instantiated to reduce to anything
      if (!from.isFunctionalTerm()) continue;

      // CASE 3: similarly, anything may reduce to a variable with no instantiation requirements!
      if (to.isVariable() && !dp2.lvars().contains(to.queryVariable())) continue;

      FunctionSymbol f = from.queryRoot();

      // CASE 4: from is headed by a defined symbol, and applied to enough arguments that a rule
      // may be applied => we assume that it can reduce to anything
      if (ruleArity.containsKey(f) && ruleArity.get(f) <= from.numberArguments()) continue;

      // CASE 5: from is a base-type theory term (whose root symbol is not a defined symbol), but
      // not necessarily instantiated to a _ground_ theory term -- then it can in principle reduce
      // to any value
      if (from.isTheoryTerm() && (to.isValue() || to.isVariable())) continue;

      // CASE 6: from is a term f s1 ... sn that isn't going to be reduced at the root, and to is a
      // functional term as well ==> then to should have the same form f t1 ... tn with each si γ
      // reducing to ti δ
      if (to.isFunctionalTerm()) {
        if (!f.equals(to.queryRoot())) return false;
        if (from.numberArguments() != to.numberArguments()) return false;
        for (int i = from.numberArguments(); i > 0; i--) {
          todo.push(new Pair<Term,Term>(from.queryArgument(i), to.queryArgument(i)));
        }
        continue;
      }

      // CASE 7: in the only remaining case, from is a term f s1 ... sn (with n < arity(f)) and to
      // is a var term F t1 ... tm. While this should not really happen (since it means that the
      // left-hand side of dp2 is not a pattern), let's account for it anyway
      if (to.numberArguments() > from.numberArguments()) return false;
      if (!to.queryHead().isVariable()) return false;
      for (int i = 0; i < to.numberArguments(); i++) {
        Term a = from.queryArgument(from.numberArguments()-i);
        Term b = to.queryArgument(to.numberArguments()-i);
        if (!a.queryType().equals(b.queryType())) return false;
        todo.push(new Pair<Term,Term>(a, b));
      }
    }
    return !(TermAnalyser.satisfy(requirements, Settings.smtSolver)
             instanceof TermAnalyser.Result.NO);
  }
}
