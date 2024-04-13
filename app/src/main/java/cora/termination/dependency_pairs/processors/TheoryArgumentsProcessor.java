package cora.termination.dependency_pairs.processors;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.TreeMap;
import charlie.types.Type;
import charlie.terms.FunctionSymbol;
import charlie.terms.Variable;
import charlie.terms.Term;
import cora.io.OutputModule;
import cora.config.Settings;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;

public class TheoryArgumentsProcessor implements Processor {
  private TreeMap<FunctionSymbol,TreeSet<Integer>> _targs;

  /** This technique can be disabled by runtime arguments. */
  public static String queryDisabledCode() { return "tharg"; }

  public boolean isApplicable(Problem dp) { return !Settings.isDisabled(queryDisabledCode()); }

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

  private class TAProofObject extends ProcessorProofObject {
    public TAProofObject(Problem inp) { super(inp); }
    public TAProofObject(Problem inp, Problem out) { super(inp, out); }
    public TAProofObject(Problem inp, List<Problem> out) { super(inp, out); }
    public String queryProcessorName() { return "Theory Arguments"; }
    public void justify(OutputModule module) {
      if (_output.size() == 1) {
        module.println("We use the following theory arguments function, which fixes all public " +
          "dependency pairs:");
      }
      else module.println("We use the following theory arguments function:");
      module.startTable();
      for (FunctionSymbol f : _targs.keySet()) {
        module.nextColumn("%a", f.toString());
        module.nextColumn(":");
        module.println("%a", _targs.get(f).toString());
      }
      module.endTable();
      if (_output.size() == 1) module.println("This yields:");
      else module.println("This yields the following new DP problems:");
    }
  }

  public ProcessorProofObject transform(Problem dpp) {
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
    if (!anythingChanged) return new TAProofObject(dpp);

    Problem ret = new Problem(newdps, dpp.getTRS());

    return new TAProofObject(dpp, ret);
  }

  public TAProofObject processDPP(Problem dpp) {
    setupInitialArgumentsFunction(dpp);
    imposeMinimalLimitations(dpp);
    imposeConsistencyLimitations(dpp);
    int numfixed = 0;
    for (DP dp : dpp.getDPList()) {
      if (checkFixes(dp)) numfixed++;
    }
    if (numfixed == dpp.getDPList().size()) return new TAProofObject(dpp); // can't improve on that!
    if (numfixed == 0) {
      // It is very possible that we could improve in this case, but then we'd have to start trying
      // out different DPs to fix.  For now, we have not implemented this.
      return new TAProofObject(dpp);
    }
    ArrayList<DP> newdpsA = new ArrayList<DP>();
    ArrayList<DP> newdpsB = new ArrayList<DP>();
    for (DP dp : dpp.getDPList()) {
      if (checkFixes(dp)) newdpsA.add(dp);
      else {
        newdpsB.add(dp);
        newdpsA.add(updateVariables(dp));
      }
    }
    Problem retA = new Problem(newdpsA, dpp.getTRS());
    Problem retB = new Problem(newdpsB, dpp.getTRS());

    return new TAProofObject(dpp, List.of(retA, retB));
  }
}
