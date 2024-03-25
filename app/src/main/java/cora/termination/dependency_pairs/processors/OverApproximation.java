package cora.termination.dependency_pairs.processors;

import cora.exceptions.NullInitialisationError;
import cora.utils.Pair;
import cora.types.TypeFactory;
import cora.terms.*;
import cora.trs.TRS;
import cora.theorytranslation.TermAnalyser;
import cora.config.Settings;
import cora.termination.dependency_pairs.DP;
import org.jetbrains.annotations.NotNull;
import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

class OverApproximation {

  private TRS _trs;

  public OverApproximation(@NotNull TRS trs) {
    if (trs == null) throw new NullInitialisationError("OverApproximation", "trs argument.");
    _trs = trs;
  }

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

    List<Variable> theory = new ArrayList<>();
    for (Variable x : dp.vars()) {
      if (subst.get(x) != null) theory.add(subst.get(x).queryVariable());
    }
    return new DP(newleft, newright, newconstraint, theory, dp.isPrivate());
  }

  private Term makeAnd(Term phi, Term psi) {
    return TermFactory.createApp(TheoryFactory.andSymbol, phi, psi);
  }

  private Term makeEqual(Term expr1, Term expr2) {
    if (expr1.queryType().equals(TypeFactory.intSort)) {
      return TermFactory.createApp(TheoryFactory.equalSymbol, expr1, expr2);
    }
    // we don't have IFF yet, so we just build it
    if (expr1.queryType().equals(TypeFactory.boolSort)) {
      Term notexpr1 = TheoryFactory.notSymbol.apply(expr1);
      Term notexpr2 = TheoryFactory.notSymbol.apply(expr2);
      Term a = TermFactory.createApp(TheoryFactory.orSymbol, notexpr1, expr2);
      Term b = TermFactory.createApp(TheoryFactory.orSymbol, notexpr2, expr1);
      return TermFactory.createApp(TheoryFactory.andSymbol, a, b);
    }
    // no idea what to do with other types for now
    return TheoryFactory.createValue(true);
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

  private boolean allVarsInTheory(Environment<Variable> vars, List<Variable> theory) {
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
      if (from.isTheoryTerm() && !from.queryType().isArrowType() &&
        !from.queryType().isArrowType() && allVarsInTheory(from.vars(), dp1.vars())) {
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
      if (to.isVariable() && !dp2.vars().contains(to.queryVariable())) continue;

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
    return TermAnalyser.satisfy(requirements, Settings.smtSolver) != null;
  }
}
