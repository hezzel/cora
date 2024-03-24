package cora.termination.dependency_pairs.processors;

import charlie.util.Pair;
import charlie.smt.*;
import cora.io.OutputModule;
import cora.config.Settings;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import cora.terms.FunctionSymbol;
import cora.terms.Term;

import java.util.Optional;
import java.util.*;

public class SubtermProcessor implements Processor {

  private SmtProblem _smt;

  @Override
  public boolean isApplicable(Problem dp) { return true; }

  /**
   * Generates an Integer variable, i.e.,
   * an object of type {@link IVar}, for each
   * @param dpp
   * @return
   */
  private Map<FunctionSymbol, IVar> generateFnIvarMap(Problem dpp) {
    //TODO Refactor this function, it is highly non-efficient.
    Set<FunctionSymbol> allFns = dpp.getSharpHeads();

    Map<FunctionSymbol, IVar> retMap = new TreeMap<>();

    // TODO: I am getting a list here, which defeats the point of having sets.
    //  Fix this later.
    allFns
      .stream()
      .forEach(fn -> retMap.put(fn, _smt.createIntegerVariable()));
    return retMap;
  }

  private Map<DP, BVar> generateDpBVarMap(Problem dpp) {
    Map<DP, BVar> retMap = new LinkedHashMap<>(dpp.getDPList().size());
    dpp.getDPList()
      .forEach(dp -> retMap.put(dp, _smt.createBooleanVariable()));
    return retMap;
  }

  private void addFnConstraintsToSMT(Map<FunctionSymbol, IVar> map) {
    map.forEach (
      (fn, ivar) -> {
        int arity = fn.queryArity();
        _smt.require(SmtFactory.createLeq(SmtFactory.createValue(1),  ivar));
        _smt.require(SmtFactory.createGeq(SmtFactory.createValue(arity), ivar));
      }
    );
  }

  private void requireAtLeastOneStrict(Map<DP, BVar> boolMap) {
    ArrayList<Constraint> disj = new ArrayList<Constraint>();
    for (BVar b : boolMap.values()) {
      disj.add(b);
    }
    _smt.require(SmtFactory.createDisjunction(disj));
  }

  // TODO this function doesn't belong here...
  //  it implements the subterm relation s >= t.
  //  meaning s = t or <the normal subterm relation>
  private boolean isSubtermGTE(Term s, Term t) {
    if (s.equals(t)) {
      return true;
    } else {
        return
          s.querySubterms()
          .stream()
          .map(Pair::fst)
          .toList()
          .contains(t);
    }
  }

  private void addProblemConstraintsToSMT(Map<FunctionSymbol, IVar> fSharpMap, Map<DP, BVar> dpbVarMap, Problem dpp) {
    for (DP dp : dpp.getDPList()) {
      Term lhs = dp.lhs();
      FunctionSymbol f = lhs.queryRoot();
      Term rhs = dp.rhs();
      FunctionSymbol g = rhs.queryRoot();
      for (int i = 1; i <= lhs.queryArguments().size(); i++) {
        for (int j = 1; j <= rhs.queryArguments().size(); j++) {
          if (f.equals(g) && i != j) continue;
          Term si = lhs.queryArgument(i);
          Term tj = rhs.queryArgument(j);
          //
          Constraint c0 = SmtFactory.createUnequal(fSharpMap.get(f), SmtFactory.createValue(i));
          Constraint c1 = SmtFactory.createUnequal(fSharpMap.get(g), SmtFactory.createValue(j));
          if (si.equals(tj)) {
            Constraint c2 = SmtFactory.createNegation(dpbVarMap.get(dp));
            Constraint disjunction = SmtFactory.createDisjunction(new ArrayList<>(List.of(c0, c1, c2)));
            _smt.require(disjunction);
          } else if (isSubtermGTE(si, tj)) {
            Constraint c2 = dpbVarMap.get(dp);
            Constraint disjunction = SmtFactory.createDisjunction(new ArrayList<>(List.of(c0, c1, c2)));
            _smt.require(disjunction);
          } else {
            Constraint disjunction = SmtFactory.createDisjunction(new ArrayList<>(List.of(c0, c1)));
            _smt.require(disjunction);
          }
        }
      }
    }
  }

  private class SubcritProofObject extends ProcessorProofObject {
    public SubcritProofObject(Problem inp) { super(inp); }
    public SubcritProofObject(Problem inp, Problem out) { super(inp, out); }
    public SubcritProofObject(Problem inp, List<Problem> out) { super(inp, out); }
    public void justify(OutputModule module) { }
    public String queryProcessorName() { return "Subterm Criterion"; }
  }

  @Override
  public ProcessorProofObject processDPP(Problem dpp) {
    _smt = new SmtProblem();

    // Generates an IntegerSMT variable for each f-sharp symbol
    Map<FunctionSymbol, IVar> fSharpMap = generateFnIvarMap(dpp);
    // Adds the respective constraints to the smt state
    addFnConstraintsToSMT(fSharpMap);
    // Generates boolean variables for each DP
    Map<DP, BVar> dpbVarMap = generateDpBVarMap(dpp);
    // Requires that at least one DP is oriented strictly
    requireAtLeastOneStrict(dpbVarMap);
    // Adds all the constraints of this dpp to the smt solver
    addProblemConstraintsToSMT(fSharpMap, dpbVarMap, dpp);

    // Ask the SMT-solver to find the projection function for us.
    Valuation valuation = null;
    switch (Settings.smtSolver.checkSatisfiability(_smt)) {
      case SmtSolver.Answer.YES(Valuation val): valuation = val; break;
      default: return new SubcritProofObject(dpp); // this processor cannot do anything
    };

    // we found a solution! Store the information from the valuation
    TreeSet<Integer> indexOfOrientedDPs = new TreeSet<>();
    TreeMap<FunctionSymbol,Integer> nu = new TreeMap<FunctionSymbol,Integer>();
    List<DP> originalDPs = dpp.getDPList();
    Valuation v = valuation;  // local variables referenced from a lambda expression must be effectively final
    fSharpMap.forEach(
      (f, ivar) -> {
        nu.put(f, v.queryAssignment(ivar));
      });
    for (int index = 0; index < originalDPs.size(); index++) {
      DP dp = originalDPs.get(index);
      BVar bvar = dpbVarMap.get(dp);
      if (valuation.queryAssignment(bvar)) { indexOfOrientedDPs.add(index); }
    }

    return new SubtermCriterionProof(dpp, indexOfOrientedDPs, nu);
  }
}
