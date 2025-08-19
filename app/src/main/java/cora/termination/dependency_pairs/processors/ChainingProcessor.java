package cora.termination.dependency_pairs.processors;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.LinkedList;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import charlie.util.Pair;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.*;
import charlie.trs.TRS;
import cora.io.OutputModule;
import cora.config.Settings;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;

/**
 * Chains consecutive DPs in the DP graph into new DPs that have the same
 * top rewrite relation as the consecutive DPs. For example, from
 * <pre>
 *     f#(x, y) -> g#(x+1, y-1) | x < y ∧ y > 42
 *     g#(x, y) -> h#(x+7, 3*y) | x < y ∧ y > 42
 * </pre>
 * we will get
 * <pre>
 *     f#(x, y) -> h#((x+1)+7, 3*(y-1)) | x < y ∧ y > 42 ∧ x+1 < y-1 ∧ y-1 > 42
 * </pre>
 */
public class ChainingProcessor implements Processor {

  /** May a DP f# ... => f# ... be chained with itself? */
  private final boolean _allowSelfChaining;

  /**
   * Constructs a new ChainingProcessor.
   *
   * @param allowSelfChaining may a DP f# ... => f# ... be chained with itself
   *                          by this processor?
   */
  public ChainingProcessor(boolean allowSelfChaining) {
    _allowSelfChaining = allowSelfChaining;
  }

  /** This technique can be disabled by runtime arguments. */
  public static String queryDisabledCode() { return "chaining"; }

  @Override
  public boolean isApplicable(Problem dpp) {
    if (Settings.isDisabled(queryDisabledCode())) return false;
    if (!dpp.isInnermost()) return false;
      // TODO: check if this processor is also applicable in full rewriting if the
      // computability or termination flag is set
    return dpp.getDPList().size() >= (_allowSelfChaining ? 1 : 2);
      // TODO not applicable if there are non-values in arguments of the lhs
      // of some DP (currently caught in processDPP)
  }

  @Override
  public ProcessorProofObject processDPP(Problem dpp) {
    // find function symbol to merge away using some heuristics
    // (or do max merge in 1 step?)

    // f# |-> { f# ... => g# ... [...] } where the DPs are taken from dpp
    Map<FunctionSymbol, Set<DP>> rootToDP1s = new LinkedHashMap<>();
    // f# |-> { e# ... => f# ... [...] } where the DPs are taken from dpp
    Map<FunctionSymbol, Set<DP>> rootToDP2s = new LinkedHashMap<>();
    // these symbols must not be at the root of the lhs of a DP2
    Set<FunctionSymbol> forbiddenDP2Roots = new LinkedHashSet<>();

    // put correct information into the above vars
    classifyDPs(dpp, rootToDP1s, rootToDP2s, forbiddenDP2Roots);

    // We need a head symbol g# such that there are DP1 = f# ... -> g# ... and
    // DP2 = g# ... -> h# ... for some f#, h# (which may be identical and may
    // be g#).
    // Additionally, all arguments of the lhss of DP1 and DP2 must be values,
    // and the rhs of DP2 must not contain subterms that could match the lhs
    // of a rule.
    SortedSet<Pair<FunctionSymbol, Integer>> headsToTry =
      chooseHeadCandidates(rootToDP1s, rootToDP2s, forbiddenDP2Roots);

    // try all candidate heads in increasing score
    outer: for (Pair<FunctionSymbol, Integer> chosenHeadsWithScore : headsToTry) {
      FunctionSymbol chosenHead = chosenHeadsWithScore.fst();
      Set<DP> dp1s = rootToDP1s.get(chosenHead);
      Set<DP> dp2s = rootToDP2s.get(chosenHead);
      Map<DP, Pair<DP, DP>> chainedToOldDPs = new LinkedHashMap<>();
      for (DP dp1 : dp1s) {
        for (DP dp2 : dp2s) {
          Optional<DP> dpNewOrEmpty = chainDPs(dp1, dp2);
          if (dpNewOrEmpty.isEmpty()) {
            continue outer; // try next
          }
          DP dpChained = dpNewOrEmpty.get();
          chainedToOldDPs.put(dpChained, new Pair<>(dp1, dp2));
        }
      }
      // prepare result
      Set<DP> deletedDPs = new LinkedHashSet<>(dp1s);
      deletedDPs.addAll(dp2s);
      Set<DP> dpsResult = new LinkedHashSet<>(dpp.getDPList());
      dpsResult.removeAll(deletedDPs);
      dpsResult.addAll(chainedToOldDPs.keySet());

      // TODO check use of new constructor API for Problem
      Problem result = new Problem(new ArrayList<>(dpsResult), dpp.getRuleList(),
        null, dpp.getOriginalTRS(), dpp.isInnermost(), dpp.hasExtraRules(),
        dpp.queryTerminationStatus());
      return new ChainingProof(dpp, result, chainedToOldDPs, deletedDPs);
    }
    // no function symbol could be chained away
    return new ChainingProof(dpp);
  }

  private static void classifyDPs(Problem dpp,
                                  Map<FunctionSymbol, Set<DP>> rootToDP1s,
                                  Map<FunctionSymbol, Set<DP>> rootToDP2s,
                                  Set<FunctionSymbol> forbiddenDP2Roots) {
    Set<FunctionSymbol> heads = dpp.getHeads();
    for (FunctionSymbol fSharp : heads) {
      rootToDP1s.put(fSharp, new LinkedHashSet<>()); // init
      rootToDP2s.put(fSharp, new LinkedHashSet<>()); // init
    }
    TRS trs = dpp.getOriginalTRS();
    Set<FunctionSymbol> definedSymbols = trs.definedSymbols();
    // presuming that the original TRS is up to date wrt the current DP problem
    // (may be an issue, e.g., after using Semantic Labelling)

    List<DP> allDPs = dpp.getDPList();
    for (DP dp : allDPs) {
      Term lhs = dp.lhs();
      Term rhs = dp.rhs();
      FunctionSymbol lhsRoot = lhs.queryRoot();
      FunctionSymbol rhsRoot = rhs.queryRoot();
      // any calls to rules from R in the rhs of DP1?
      // if so, no DPs ... => f# ... is eligible as a DP1
      Set<FunctionSymbol> rhsSymbols = new LinkedHashSet<>();
      rhs.storeFunctionSymbols(rhsSymbols);
      if (!Collections.disjoint(definedSymbols, rhsSymbols)) {
        forbiddenDP2Roots.add(rhsRoot);
      }
      Set<DP> dp1s = rootToDP1s.get(rhsRoot);
      dp1s.add(dp); // actually not needed if the rhs contains defined symbols
      // DP2s are allowed to have function calls
      Set<DP> dp2s = rootToDP2s.get(lhsRoot);
      dp2s.add(dp);
    }
  }

  private SortedSet<Pair<FunctionSymbol, Integer>>
      chooseHeadCandidates(Map<FunctionSymbol, Set<DP>> rootToDP1s,
                           Map<FunctionSymbol, Set<DP>> rootToDP2s,
                           Set<FunctionSymbol> forbiddenDP2Roots) {
    // order by smallest |newDPs| - |oldDPs|; in case of a tie by function symbol
    Comparator<Pair<FunctionSymbol, Integer>> cmp = (p1, p2) -> {
      int p1snd = p1.snd();
      int p2snd = p2.snd();
      return p1snd != p2snd ? p1snd - p2snd : p1.fst().compareTo(p2.fst());
    };
    SortedSet<Pair<FunctionSymbol, Integer>> result = new TreeSet<>(cmp);
    for (Map.Entry<FunctionSymbol, Set<DP>> rootToDP1Entry : rootToDP1s.entrySet()) {
      FunctionSymbol root = rootToDP1Entry.getKey();
      if (forbiddenDP2Roots.contains(root)) { // don't chain this one
        continue;
      }
      Set<DP> dp1s = rootToDP1Entry.getValue();
      Set<DP> dp2s = rootToDP2s.get(root);
      if (!_allowSelfChaining && !Collections.disjoint(dp1s, dp2s)) {
        continue; // we could self-chain a DP, but the processor config says no
      }
      // all old DPs are deleted; their cross product wrt chaining is created
      int size1 = dp1s.size();
      int size2 = dp2s.size();
      int sizeNew = size1 * size2; // each dp1 is chained with each dp2

      if (sizeNew == 0) {
        continue; // if we don't continue here, we may remove a DP instead of chaining it
      }

      int sizeOld = size1 + size2; // all chained DPs are deleted
      int sizeDiff = sizeNew - sizeOld;
      result.add(new Pair<>(root, sizeDiff));
    }
    return result;
  }

  /**
   * Chains a DP e# ... => f# ... [ phi ] and a DP f# ... => g# ... [ phi']
   * to a DP e# ... => g# ... [ phi'' ] for suitable phi'' and suitable
   * substitutions applied to ...
   *
   * @param dp1 the first DP to chain
   * @param dp2 the second DP to chain
   * @return the DP resulting from chaining left and right if this is possible;
   *  empty otherwise
   */
  private static Optional<DP> chainDPs(DP dp1, DP dp2) {
    // TODO use unification instead of matching to make method more applicable
    dp2 = dp2.getRenamed();
    Term dp1Rhs = dp1.rhs();
    Term dp2Lhs = dp2.lhs();

    Substitution matcher = dp2Lhs.match(dp1Rhs);
    if (matcher == null) {
      return Optional.empty();
    }
    // check whether all logical variables of right are mapped to theory terms

    Set<Replaceable> replaceables = new LinkedHashSet<>(matcher.domain());
    replaceables.retainAll(dp2.lvars());
    for (Replaceable var : replaceables) {
      // replacement should not be null: var is in the domain of matcher
      Term replacement = matcher.get(var);
      if (! replacement.isTheoryTerm()) {
        return Optional.empty();
      }
    }
    Term resultRhs = dp2.rhs().substitute(matcher);
    Term dp2ConstraintSubst = dp2.constraint().substitute(matcher);
    Term resultConstraint = TermFactory.createApp(TheoryFactory.andSymbol,
      dp1.constraint(), dp2ConstraintSubst);
    Set<Variable> resultTheoryVars = new LinkedHashSet<>(dp1.lvars());
    for (Variable x : dp2.lvars()) {
      Term xReplacement = matcher.get(x);
      Environment<Variable> env = xReplacement.vars();
      for (Variable v : env) {
        resultTheoryVars.add(v);
      }
    }
    DP result = new DP(dp1.lhs(), resultRhs, resultConstraint, resultTheoryVars);
    return Optional.of(result);
  }

  private static class ChainingProof extends ProcessorProofObject {
    private final Map<DP, Pair<DP, DP>> _chainedToOriginalDPs;
    private final Set<DP> _deletedDPs;

    public ChainingProof(Problem input) {
      super(input);
      _chainedToOriginalDPs = null;
      _deletedDPs = null;
    }

    public ChainingProof(Problem input, Problem output,
                         Map<DP, Pair<DP, DP>> chainedToOriginalDPs,
                         Set<DP> deletedDPs) {
      super(input, output);
      _chainedToOriginalDPs = chainedToOriginalDPs;
      _deletedDPs = deletedDPs;
    }

    /**
     * Gets a Renaming that allows the given 3 DPs to be printed at the same time (so with
     * their variables consistently named).
     */
    private Renaming getRenaming(OutputModule module, DP dp1, DP dp2, DP dp3) {
      Set<Variable> allvars = dp1.getAllVariables();
      Term[] vars = new Term[allvars.size()];
      int i = 0;
      for (Variable x : dp1.getAllVariables()) vars[i++] = x;
      MutableRenaming ret = module.generateUniqueNaming(vars);
      for (Variable x : dp2.getAllVariables()) extend(ret, x);
      for (Variable x : dp3.getAllVariables()) extend(ret, x);
      return ret;
    }

    /** Helper function for getRenaming: extends the given renaming with a name for x */
    private void extend(MutableRenaming renaming, Variable x) {
      if (renaming.getName(x) != null) return;
      String name = x.queryName();
      while (!renaming.isAvailable(name)) name += "'";
      renaming.setName(x, name);
    }

    @Override
    public void justify(OutputModule module) {
      if (_output == null) {
        module.println("No suitable chaining could be found.");
        return;
      }
      module.println("We chain DPs according to the following mapping:");
      module.println();
      module.startTable();
      _chainedToOriginalDPs.forEach(
        (c, p) -> {
          Renaming renaming = getRenaming(module, c, p.fst(), p.snd());
          module.nextColumn("%a", new Pair<DP,Renaming>(c, renaming));
          module.nextColumn(" is obtained by chaining ");
          module.nextColumn("%a", new Pair<DP,Renaming>(p.fst(), renaming));
          module.nextColumn("and");
          module.nextColumn("%a", new Pair<DP,Renaming>(p.snd(), renaming));
          module.println();
        }
      );
      module.endTable();
      module.println();
      module.println("The following DPs were deleted:");
      _deletedDPs.forEach(dp -> module.println("%a", dp));
      module.println();
      module.println("By chaining, we added " + _chainedToOriginalDPs.size()
        + " DPs and removed " + _deletedDPs.size() + " DPs.");
    }

    @Override
    public String queryProcessorName() {
      return "Chaining Processor";
    }
  }
}
