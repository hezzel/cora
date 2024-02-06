package cora.termination.dependency_pairs.processors;

import cora.smt.*;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import cora.terms.FunctionSymbol;
import cora.terms.Term;
import cora.types.Type;
import cora.types.TypeFactory;
import cora.utils.Pair;

import java.util.*;

public class SubtermProcessor implements Processor {

  private final SmtProblem _smt = new SmtProblem();
  private static final Type _dpSort = TypeFactory.createSort("DP_SORT");

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
        _smt.require(SmtProblem.createLeq(SmtProblem.createValue(1),  ivar));
        _smt.require(SmtProblem.createGeq(SmtProblem.createValue(arity), ivar));
      }
    );
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

    addFnConstraintsToSMT(fSharpMap);

    for (DP dp : dpp.getDPList()) {
      Term lhs = dp.lhs();
      FunctionSymbol f = lhs.queryRoot();
      Term rhs = dp.rhs();
      FunctionSymbol g = rhs.queryRoot();
      for(int i = 1; i <= lhs.queryArguments().size(); i++) {
        for (int j = 1; j <= rhs.queryArguments().size(); j++) {
          Term si = lhs.queryArgument(i);
          Term tj = rhs.queryArgument(j);
          //
          Constraint c0 = SmtProblem.createUnequal(fSharpMap.get(f), SmtProblem.createValue(i));
          Constraint c1 = SmtProblem.createUnequal(fSharpMap.get(g), SmtProblem.createValue(j));
          if (si.equals(tj)) {
            Constraint c2 = SmtProblem.createNegation(dpbVarMap.get(dp));
            Constraint disjunction = SmtProblem.createDisjunction(new ArrayList<>(List.of(c0, c1, c2)));
            _smt.require(disjunction);
          } else if (isSubtermGTE(si, tj)) {
            System.out.println(tj + " is a subtterm of " + si);
            Constraint c2 = dpbVarMap.get(dp);
            Constraint disjunction = SmtProblem.createDisjunction(new ArrayList<>(List.of(c0, c1, c2)));
            _smt.require(disjunction);
          } else {
            System.out.println(tj + " is not subterm of " + si);
            Constraint disjunction = SmtProblem.createDisjunction(new ArrayList<>(List.of(c0, c1)));
            _smt.require(disjunction);
          }
        }
      }
    }
  }

  @Override
  public List<Problem> processDPP(Problem dpp) {
    // Generates an IntegerSMT variable for each f-sharp symbol
    Map<FunctionSymbol, IVar> fSharpMap = generateFnIvarMap(dpp);
    // System.out.println("Mappings of fsharps: " + fSharpMap);
    // Adds the respective constraints to the smt state
    addFnConstraintsToSMT(fSharpMap);
    // Generates boolean variables for each DP
    Map<DP, BVar> dpbVarMap = generateDpBVarMap(dpp);

    // Adds all the constraints of this dpp to the smt solver
    addProblemConstraintsToSMT(fSharpMap, dpbVarMap, dpp);

    //
    Valuation valuation = _smt.satisfy();

    if (valuation == null) {
      // this processor cannot do anything
      return new ArrayList<>(List.of(dpp));
    } else {
      List<Integer> indexOfOrientedDPs = new ArrayList<>();
      dpbVarMap.forEach (
        (dp, bvar) -> {
          if (valuation.queryAssignment(bvar)) { indexOfOrientedDPs.add(dpp.getDPList().indexOf(dp)); }
          System.out.println("Boolean value found for the dp " + dp + " is " + valuation.queryAssignment(bvar));
        });

      List<DP> removedDPs = new ArrayList<>(List.copyOf(dpp.getDPList()));

      for (int indexToRemove : indexOfOrientedDPs) {
        removedDPs.remove(indexToRemove);
      }

      GraphProcessor gProc = new GraphProcessor();

      return gProc.processDPP(new Problem(removedDPs, dpp.getTRS()));
    }
  }

}
