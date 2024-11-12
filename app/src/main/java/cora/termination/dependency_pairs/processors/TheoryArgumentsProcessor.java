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
import charlie.terms.TheoryFactory;
import charlie.trs.TrsProperties.*;
import cora.io.OutputModule;
import cora.config.Settings;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;

public class TheoryArgumentsProcessor implements Processor {
  private boolean _fixPublic;
  private TreeMap<FunctionSymbol,TreeSet<Integer>> _targs;

  public static String queryDisabledCode() { return "thargs"; }

  /**
   * Generate one of the two theory arguments processors.
   *
   * @param fixPublic if set to true, this will generate the theory arguments processor that fixes
   *   public dependency pairs (so that always returns only one DP problem, with the same number of
   *   DPS as the original).  If set to false, this will generate the general theory arguments
   *   processor that fixes an arbitrary DP (so that will always return two DP problems).
   */
  public TheoryArgumentsProcessor(boolean fixPublic) {
    _fixPublic = fixPublic;
  }

  public static TheoryArgumentsProcessor generalTArgsProcessor() {
    return new TheoryArgumentsProcessor(false);
  }

  public boolean isApplicable(Problem dpp) {
    return !Settings.isDisabled(queryDisabledCode()) &&
           (!_fixPublic || dpp.hasPrivateDPs()) &&
           dpp.getOriginalTRS().verifyProperties(Level.APPLICATIVE, Constrained.YES,
                                                 TypeLevel.SIMPLE, Lhs.PATTERN, Root.THEORY);
  }

  /**
   * Sets up _targs to map each f in Heads(dpp) to the set of all argument positions of theory
   * sort.
   */
  private void setupInitialArgumentsFunction(Problem dpp) {
    _targs = new TreeMap<FunctionSymbol,TreeSet<Integer>>();
    Set<FunctionSymbol> allFns = dpp.getHeads();
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
      TreeSet<Variable> goodvars = new TreeSet<Variable>(dp.lvars());
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
        if (!dp.lvars().contains(x)) return false;
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
        if (!dp.lvars().contains(x)) {
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
  private DP updateVariables(DP dp, boolean innermost) {
    TreeSet<Variable> newvars = new TreeSet<Variable>(dp.lvars());
    Term lhs = dp.lhs();
    FunctionSymbol f = lhs.queryRoot();
    Term constraint = dp.constraint();
    for (int i : _targs.get(f)) {
      Term arg = lhs.queryArgument(i);
      for (Variable x : arg.vars()) {
        newvars.add(x);
        if (innermost) {
          Term eq = TheoryFactory.createEquality(x, x);
          constraint = TheoryFactory.createConjunction(constraint, eq);
        }
      }
    }

    return new DP(lhs, dp.rhs(), constraint, newvars);
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
    }
  }

  public TAProofObject processDPP(Problem dpp) {
    setupInitialArgumentsFunction(dpp);
    imposeMinimalLimitations(dpp);
    if (_fixPublic) return transform(dpp);
    else return fixSomething(dpp);
  }

  /**
   * The "public" version of the processor: all the public DPs are fixed, so we only return one DP
   * problem, where "theory argument" information may be added to the private DPs.
   */
  private TAProofObject transform(Problem dpp) {
    List<DP> dps = dpp.getDPList();
    for (int i = 0; i < dps.size(); i++) {
      if (!dpp.isPrivate(i)) ensureFixes(dps.get(i));
    }
    imposeConsistencyLimitations(dpp);

    ArrayList<DP> newdps = new ArrayList<DP>();
    TreeSet<Integer> priv = new TreeSet<Integer>();
    boolean anythingChanged = false;
    for (int i = 0; i < dps.size(); i++) {
      if (checkFixes(dps.get(i))) newdps.add(dps.get(i));
      else {
        anythingChanged = true;
        newdps.add(updateVariables(dps.get(i), dpp.isInnermost()));
      }
      if (dpp.isPrivate(i)) priv.add(i);
    }
    if (!anythingChanged) return new TAProofObject(dpp);

    Problem ret = new Problem(newdps, dpp.getRuleList(), priv, dpp.getOriginalTRS(),
      dpp.isInnermost(), dpp.hasExtraRules(), dpp.queryTerminationStatus());

    return new TAProofObject(dpp, ret);
  }

  private int getNumFixed(Problem dpp) {
    int numfixed = 0;
    for (DP dp : dpp.getDPList()) {
      if (checkFixes(dp)) numfixed++;
    }
    return numfixed;
  }

  /**
   * The general verson of the processor: at least one DP is fixed, so we return two DP problems:
   * one in which the fixed DPs do not occur at all (which preserves public/private information),
   * and one in which the theory arguments function is applied to modify some of the other DPs.
   */
  private TAProofObject fixSomething(Problem dpp) {
    imposeConsistencyLimitations(dpp);
    List<DP> dps = dpp.getDPList();
    int numfixed = getNumFixed(dpp);
    if (numfixed == dps.size()) return new TAProofObject(dpp); // can't improve on that!
    if (numfixed == 0) {
      ensureFixes(dps.get(0));
      imposeConsistencyLimitations(dpp);
      numfixed = getNumFixed(dpp);
      if (numfixed == dps.size() || numfixed == 0) return new TAProofObject(dpp);
      // It is very possible that we could improve by choosing a different DP to fix, but for now
      // we just pick the first rather than iterating over all of them
    }
    ArrayList<DP> newdpsA = new ArrayList<DP>();
    ArrayList<DP> newdpsB = new ArrayList<DP>();
    TreeSet<Integer> privB = new TreeSet<Integer>();
    for (int i = 0; i < dps.size(); i++) {
      DP dp = dps.get(i);
      if (checkFixes(dp)) newdpsA.add(dp);
      else {
        if (dpp.isPrivate(i)) privB.add(newdpsB.size());
        newdpsB.add(dp);
        newdpsA.add(updateVariables(dp, dpp.isInnermost()));
      }
    }
    Problem retA = new Problem(newdpsA, dpp.getRuleList(), new TreeSet<Integer>(),
      dpp.getOriginalTRS(), dpp.isInnermost(), dpp.hasExtraRules(), dpp.queryTerminationStatus());
    Problem retB = new Problem(newdpsB, dpp.getRuleList(), privB, dpp.getOriginalTRS(),
      dpp.isInnermost(), dpp.hasExtraRules(), dpp.queryTerminationStatus());

    return new TAProofObject(dpp, List.of(retA, retB));
  }
}
