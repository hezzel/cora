package cora.termination.dependency_pairs.processors;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.TreeMap;
import cora.types.Type;
import cora.terms.FunctionSymbol;
import cora.terms.Variable;
import cora.terms.Term;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.certification.Informal;

public class TheoryArgumentsProcessor implements Processor {
  private TreeMap<FunctionSymbol,TreeSet<Integer>> _targs;

  public boolean isApplicable(Problem dpp) {
    return true;
  }

  /**
   * Sets up _targs to map each f in Heads(dpp) to the set of all argument positions of theory
   * sort.
   */
  private void setupInitialArgumentsFunction(Problem dpp) {
    _targs = new TreeMap<FunctionSymbol,TreeSet<Integer>>();
    Set<FunctionSymbol> allFns = dpp.getSharpHeads();
    for (FunctionSymbol f : allFns) {
      _targs.put(f, new TreeSet<Integer>());
      Type t = f.queryType();
      for (int i = 1; t.isArrowType(); i++, t = t.subtype(2)) {
        Type argtype = t.subtype(1);
        if (argtype.isBaseType() && argtype.isTheoryType()) _targs.get(f).add(i);
      }
    }
  }

  /**
   * This ensures that an argument position is only in targs if no non-theory symbol is every
   * passed to that argument.
   */
  private void imposeMinimalLimitations(Problem dpp) {
    ArrayList<Term> terms = new ArrayList<Term>();
    for (DP dp : dpp.getDPList()) {
      terms.add(dp.lhs());
      terms.add(dp.rhs());
    }
    for (Term term : terms) {
      FunctionSymbol root = term.queryRoot();
      TreeSet<Integer> rootset = _targs.get(root);
      for (int i = 1; i <= term.numberArguments(); i++) {
        if (rootset.contains(i) && !term.queryArgument(i).isTheoryTerm()) rootset.remove(i);
      }
    }
  }

  /**
   * This ensures that the theory arguments function is consistent: if
   * f(l1,...,lk) ⇒ g(r1,...,rm) [phi | L] then for all i in _targs[g], all variables in ti occur
   * either in L, or as a variable in some _targs[f].
   */
  private void imposeConsistencyLimitations(Problem dpp) {
    for (DP dp : dpp.getDPList()) {
      TreeSet<Variable> goodvars = new TreeSet<Variable>(dp.vars());
      FunctionSymbol f = dp.lhs().queryRoot();
      for (int i : _targs.get(f)) {
        for (Variable x : dp.lhs().queryArgument(i).vars()) {
          goodvars.add(x);
        }
      }
      FunctionSymbol g = dp.rhs().queryRoot();
      TreeSet<Integer> badindexes = new TreeSet<Integer>();
      for (int j : _targs.get(g)) {
        for (Variable x : dp.rhs().queryArgument(j).vars()) {
          if (!goodvars.contains(x)) { badindexes.add(j); break; }
        }
      }
      for (int j : badindexes) _targs.get(f).remove(j);
    }
  }

  /** This returns whether or not the current _targs fixes the given DP. */
  private boolean checkFixes(DP dp) {
    Term lhs = dp.lhs();
    FunctionSymbol f = lhs.queryRoot();
    for (int i : _targs.get(f)) {
      Term arg = lhs.queryArgument(i);
      for (Variable x : arg.vars()) {
        if (!dp.vars().contains(x)) return false;
      }
    }
    return true;
  }

  /** This function updates the theory arguments function to ensure that it fixes the given DP. */
  private void ensureFixes(DP dp) {
    Term lhs = dp.lhs();
    FunctionSymbol f = lhs.queryRoot();
    TreeSet<Integer> rootset = _targs.get(f);
    TreeSet<Integer> bad = new TreeSet<Integer>();
    for (int i : rootset) {
      Term arg = lhs.queryArgument(i);
      for (Variable x : arg.vars()) {
        if (!dp.vars().contains(x)) {
          bad.add(i);
          break;
        }
      }
    }
    for (int i : bad) rootset.remove(i);
  }

  /**
   * This returns the given DP, modified to have all variables added to the variable set that
   * are allowed by _targs.
   */
  private DP updateVariables(DP dp) {
    TreeSet<Variable> newvars = new TreeSet<Variable>(dp.vars());
    Term lhs = dp.lhs();
    FunctionSymbol f = lhs.queryRoot();
    for (int i : _targs.get(f)) {
      Term arg = lhs.queryArgument(i);
      for (Variable x : arg.vars()) {
        newvars.add(x);
      }
    }
    return new DP(dp.lhs(), dp.rhs(), dp.constraint(),
                  new ArrayList<Variable>(newvars), dp.isPrivate());
  }

  public Problem transform(Problem dpp) {
    setupInitialArgumentsFunction(dpp);
    imposeMinimalLimitations(dpp);
    for (DP dp : dpp.getDPList()) {
      if (!dp.isPrivate()) ensureFixes(dp);
    }
    imposeConsistencyLimitations(dpp);

    ArrayList<DP> newdps = new ArrayList<DP>();
    boolean anythingChanged = false;
    for (DP dp : dpp.getDPList()) {
      if (checkFixes(dp)) newdps.add(dp);
      else {
        anythingChanged = true;
        newdps.add(updateVariables(dp));
      }
    }
    if (!anythingChanged) return dpp;

    Problem ret = new Problem(newdps, dpp.getTRS());

    Informal.getInstance().addProofStep("We use a theory arguments function " + _targs +
      " that fixes all public dependency pairs.  This yields:");
    Informal.getInstance().addProofStep(ret.toString());

    return ret;
  }

  public Optional<List<Problem>> processDPP(Problem dpp) {
    return Optional.empty();
  }
}
