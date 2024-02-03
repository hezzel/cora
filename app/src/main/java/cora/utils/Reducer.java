package cora.utils;

/**
 * THIS IS NOT MEANT TO STAY.
 *
 * This is a test implementation for the generation of the DP graph.
 */

import java.util.Set;
import java.util.Stack;
import java.util.TreeSet;
import cora.terms.*;
import cora.smt.TermAnalyser;
import cora.rewriting.TRS;

public class Reducer {
  private TRS _trs;

  /**
   * WARNING: this will fail without proper warning if the given TRS has some rule whose
   * left-hand side is not a functional term.  Only call with appropriate TRSs!
   */
  public Reducer(TRS trs) {
    _trs = trs;
  }

  public record MyDP(Term left, Term right, Term constraint, Set<Variable> theory) {}

  public static MyDP rename(MyDP dp) {
    Substitution subst = TermFactory.createEmptySubstitution();
    for (Variable x : dp.left.vars()) {
      if (subst.get(x) == null) subst.extend(x, TermFactory.createVar(x.queryName(), x.queryType()));
    }
    for (Variable x : dp.right.vars()) {
      if (subst.get(x) == null) subst.extend(x, TermFactory.createVar(x.queryName(), x.queryType()));
    }
    for (Variable x : dp.constraint.vars()) {
      if (subst.get(x) == null) subst.extend(x, TermFactory.createVar(x.queryName(), x.queryType()));
    }
    Term newleft = dp.left.substitute(subst);
    Term newright = dp.right.substitute(subst);
    Term newconstraint = dp.constraint.substitute(subst);
    TreeSet<Variable> theory = new TreeSet<Variable>();
    for (Variable x : dp.theory) {
      if (subst.get(x) != null) theory.add(subst.get(x).queryVariable());
    }
    return new MyDP(newleft, newright, newconstraint, theory);
  }

  private Term makeAnd(Term phi, Term psi) {
    return TermFactory.createApp(TheoryFactory.andSymbol, phi, psi);
  }

  private Term makeEqual(Term expr1, Term expr2) {
    return TermFactory.createApp(TheoryFactory.equalSymbol, expr1, expr2);
  }

  /**
   * This returns the smallest number of arguments with which f occurs in some rule, on the
   * left-hand side.  If f is not a defined symbol, it instead returns 1 more than the maximum
   * number of arguments f can take.
   */
  int ruleArity(FunctionSymbol f) {
    if (f.isValue()) return 1;
    int ret = f.queryArity() + 1;
    for (int i = 0; i < _trs.queryRuleCount(); i++) {
      if (f.equals(_trs.queryRule(i).queryLeftSide().queryRoot())) {
        int ar = _trs.queryRule(i).queryLeftSide().numberArguments();
        if (ar < ret) ret = ar;
      }
    }
    return ret;
  }

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
  public boolean mayReduce(MyDP dp1, MyDP dp2) {
    // it's easier to use a single substitution, so make sure they have disjoint variables!
    dp2 = rename(dp2);
    // invariant: for the requirement to hold, all the pairs on the stack must be equal, and
    // requirements must be satisfiable
    Stack<Pair<Term,Term>> todo = new Stack<Pair<Term,Term>>();
    todo.push(new Pair<Term,Term>(dp1.right(), dp2.left()));
    Term requirements = makeAnd(dp1.constraint(), dp2.constraint());
    while (!todo.isEmpty()) {
      Pair<Term,Term> pair = todo.pop();
      Term from = pair.fst();
      Term to = pair.snd();

      // CASE 1: from is a base-type theory term whose variables are all instantiated by ground
      // theory terms ==> to must either be its value, or have the same either shape (in which case
      // we fall through to case 6)
      if (from.isTheoryTerm() && !from.queryType().isArrowType() &&
          !from.queryType().isArrowType() && allVarsInTheory(from.vars(), dp1.theory())) {
        if (!to.isTheoryTerm()) return false;
        if (to.isValue() || to.isVariable()) {
          requirements = makeAnd(requirements, makeEqual(from, to));
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
      if (to.isVariable() && !dp2.theory().contains(to.queryVariable())) continue;

      FunctionSymbol f = from.queryRoot();

      // CASE 4: from is headed by a defined symbol, and applied to enough arguments that a rule
      // may be applied => we assume that it can reduce to anything
      int arity = ruleArity(f);
      if (arity <= from.numberArguments()) {
        continue;
      }

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
    return TermAnalyser.satisfy(requirements) != null;
  }
}
