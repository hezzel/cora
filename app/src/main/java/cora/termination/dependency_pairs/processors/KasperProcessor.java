package cora.termination.dependency_pairs.processors;

import cora.smt.*;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.certification.Informal;
import cora.terms.*;

import java.util.*;
import java.util.function.Consumer;

public class KasperProcessor implements Processor {

  private final SmtProblem _smt = new SmtProblem();
  private Map< FunctionSymbol, List<Variable> > _fnToFreshVar;
  private Map< FunctionSymbol, List<Term> > _candidates;
  private Map<Replaceable,String> _varNaming;

  @Override
  public boolean isApplicable(Problem dpp) {
    return true;
  }

  /**
   * For a DPP problem {@code dpp}, returns a mapping of each f# : A1 => ... => An => DP_SORT
   * in heads(P) to the list of fresh variables [x1 : A1, ..., xn : An].
   */
  private Map<FunctionSymbol, List<Variable>> computeFreshVars(Problem dpp) {
    Set<FunctionSymbol> allSharps = dpp.getSharpHeads();
    _varNaming = new TreeMap<Replaceable,String>();

    Map<FunctionSymbol, List<Variable>> ret = new TreeMap<>();
    allSharps
      .forEach( fSharp -> {
        List<Variable> newVars = DPGenerator.generateVars(fSharp.queryType());
        for (int i = 0; i < newVars.size(); i++) {
          _varNaming.put(newVars.get(i), "arg_" + (i+1));
        }
        ret.put(fSharp, newVars);
      });

    return ret;
  }

  /** This computes all candidates of the form arg_i, where the ith argument is of theory sort. */
  private Map<FunctionSymbol, List<Term>> computeSimpleCandidates(Problem dpp) {
    Set<FunctionSymbol> allSharps = dpp.getSharpHeads();

    Map<FunctionSymbol, List<Term>> ret = new TreeMap<>();

    // the initial candidates are the variables generated before such that
    // they are of theory type and base type
    allSharps.forEach(fSharp -> {
      List<Term> varToTerms = _fnToFreshVar.get(fSharp)
        .stream()
        .filter( x -> x.queryType().isTheoryType() && x.queryType().isBaseType())
        .map(x -> (Term) x)
        .toList();
      ret.put(fSharp, varToTerms);
    });

    return ret;
  }

  /**
   * Given a candidate term t over variables {x_1^f,...,x_n^f}, and a term of the form f(s1,...,sn),
   * this returns t[x_1^f:=s1,...,x_n^f:=sn].
   */
  private Term instantiateCandidate(Term candidate, Term term) {
    Substitution subst = TermFactory.createEmptySubstitution();
    FunctionSymbol f = term.queryRoot();
    for (int varL = 0; varL < f.queryArity(); varL ++) {
      subst.extend(_fnToFreshVar.get(f).get(varL), term.queryArgument(varL + 1));
    }
    return candidate.substitute(subst);
  }

  /**
   * This function filters out those candidates from the candidate list which, if chosen, would not
   * generate a ground theory term with variables in theoryVars for the given term.
   */
  private void filterCandidateList(Term term, List<Variable> theoryVars) {
    List<Term> updatedCandidates = new ArrayList<Term>();
    FunctionSymbol fSharp = term.queryRoot();
    for (Term cand : _candidates.get(fSharp)) {
      Term inst = instantiateCandidate(cand, term);
      if (!inst.isTheoryTerm()) continue;
      boolean badvar = false;
      for (Variable x : inst.vars()) {
        if (!theoryVars.contains(x)) { badvar = true; break; }
      }
      if (!badvar) updatedCandidates.add(cand);
    }
    _candidates.replace(fSharp, updatedCandidates);
  }

  /**
   * This function updates the list of candidate functions, by tossing out every candidate if, in
   * any dependency pair, it would not be instantiated by a theory term.
   */
  private void updateCandidates(Problem dpp) {
    for(DP dp : dpp.getDPList()) {

      // Decomposition of this dp as lhs => rhs [ ctr | V ]
      Term lhs = dp.lhs();
      Term rhs = dp.rhs();
      Term ctr = dp.constraint();
      List<Variable> V = dp.vars();

      filterCandidateList(lhs, V);
      filterCandidateList(rhs, V);
    }
  }

  private Map<FunctionSymbol, IVar> generateIVars(Problem dpp) {
    Set<FunctionSymbol> allFns = dpp.getSharpHeads();
    Map<FunctionSymbol, IVar> retMap = new TreeMap<>();

    System.out.println(allFns);

    allFns.forEach(fSharp -> {
      retMap.put(fSharp, _smt.createIntegerVariable());
    });
    return retMap;
  }

  private Map<DP, BVar> generateDpBVarMap(Problem dpp) {
    Map<DP, BVar> retMap = new LinkedHashMap<>(dpp.getDPList().size());
    dpp.getDPList()
      .forEach(dp -> retMap.put(dp, _smt.createBooleanVariable()));
    return retMap;
  }

  private void requiresCtrs(Map<FunctionSymbol, IVar> intMap) {
    intMap.forEach( (f, ivar) -> {
      int upperBound = _candidates.get(f).size()-1;
      _smt.require(SmtProblem.createLeq(SmtProblem.createValue(0), ivar));
      _smt.require(SmtProblem.createLeq(ivar, SmtProblem.createValue(upperBound)));
    });
  }

  private void requireAtLeastOneStrict(Map<DP, BVar> boolMap) {
    ArrayList<Constraint> disj = new ArrayList<Constraint>();
    for (BVar b : boolMap.values()) disj.add(b);
    _smt.require(SmtProblem.createDisjunction(disj));
  }

  private void putDpRequirements(Map<FunctionSymbol, IVar> intMap, Map<DP, BVar> boolMap, Problem dpp) {
    for (DP dp : dpp.getDPList()) {
      Term lhs = dp.lhs();
      Term rhs = dp.rhs();
      Term ctr = dp.constraint();

      FunctionSymbol lhsHead = lhs.queryRoot();
      FunctionSymbol rhsHead = rhs.queryRoot();

      for (int i = 0; i < _candidates.get(lhsHead).size(); i++) {
        for (int j = 0; j < _candidates.get(rhsHead).size(); j++) {
          if (lhsHead.equals(rhsHead) && i != j) continue;

          Term instLi = instantiateCandidate(_candidates.get(lhsHead).get(i), lhs);
          Term instRj = instantiateCandidate(_candidates.get(rhsHead).get(j), rhs);

          SmtProblem validityProblem = new SmtProblem();

          // translate the constraint and instantiated candidates to smt language
          Constraint constraintTranslation =
            TermSmtTranslator.translateConstraint(ctr, validityProblem);
          IntegerExpression candLiExpr =
            TermSmtTranslator.translateIntegerExpression(instLi, validityProblem);
          IntegerExpression candRjExpr =
            TermSmtTranslator.translateIntegerExpression(instRj, validityProblem);
          
          // fSharpDisjunction = nu(leftroot) != i \/ nu(rightroot) != j
          Constraint fSharpDisjunction =
            SmtProblem.createDisjunction (
              SmtProblem.createUnequal(intMap.get(lhsHead), SmtProblem.createValue(i)),
              SmtProblem.createUnequal(intMap.get(rhsHead), SmtProblem.createValue(j))
            );

          // check one: if left ≥ right doesn't even hold, then we can't have that choice of
          // candidates
          validityProblem
            .requireImplication(constraintTranslation, SmtProblem.createGeq(candLiExpr, candRjExpr));
          if (!validityProblem.isValid()) {
            _smt.require(fSharpDisjunction);
            continue;
          }

          // check two: if left > right holds, then having this choice of candidates means that the
          // DP is oriented strictly; if it doesn't, then it means the DP is not oriented strictly
          validityProblem.clear();
          validityProblem.requireImplication (
            constraintTranslation,
            SmtProblem.createConjunction (
              SmtProblem.createGeq(candLiExpr, SmtProblem.createValue(0)),
              SmtProblem.createGreater(candLiExpr, candRjExpr)
            ));

          if(validityProblem.isValid()) {
            _smt.require(
              SmtProblem.createDisjunction(
                fSharpDisjunction,
                boolMap.get(dp)
              ));
          } else {
            _smt.require (
              SmtProblem.createDisjunction(
                fSharpDisjunction,
                SmtProblem.createNegation(boolMap.get(dp))
              ));
          }
        }
      }
    }
  }

  @Override
  public Optional<List<Problem>> processDPP(Problem dpp) {

    _fnToFreshVar = computeFreshVars(dpp);

    _candidates = computeSimpleCandidates(dpp);

    updateCandidates(dpp);

    Map<FunctionSymbol, IVar> intMap = generateIVars(dpp);
    requiresCtrs(intMap);
    Map<DP, BVar> boolMap = generateDpBVarMap(dpp);
    requireAtLeastOneStrict(boolMap);
    putDpRequirements(intMap, boolMap, dpp);

    Valuation result = _smt.satisfy();

    if(result == null) return Optional.empty();

    // we found a solution! Store the information from the valuation
    TreeSet<Integer> indexOfOrientedDPs = new TreeSet<>();
    TreeMap<FunctionSymbol,Term> candFun = new TreeMap<FunctionSymbol,Term>();
    List<DP> originalDPs = dpp.getDPList();
    List<DP> remainingDPs = new ArrayList<DP>();
    intMap.forEach(
      (f, ivar) -> {
        candFun.put(f, _candidates.get(f).get(result.queryAssignment(ivar)));
      }); 
    for (int index = 0; index < originalDPs.size(); index++) {
      DP dp = originalDPs.get(index);
      BVar bvar = boolMap.get(dp);
      if (result.queryAssignment(bvar)) { indexOfOrientedDPs.add(index); }
      else { remainingDPs.add(dp); }
    }  

    // now let's generate output to the user
    Informal.getInstance().addProofStep("We apply the integer function criterion with the " +
      "following projection function.");
    candFun.forEach(
      (f, cand) -> {
        StringBuilder builder = new StringBuilder("J( " + f.toString() + " ) = ");
        cand.addToString(builder, _varNaming);
        Informal.getInstance().addProofStep(builder.toString());
      });
    Informal.getInstance().addProofStep("We thus have: ");
    for (int index = 0; index < originalDPs.size(); index++) {
      DP dp = originalDPs.get(index);
      String left = instantiateCandidate(candFun.get(dp.lhs().queryRoot()), dp.lhs()).toString();
      String right = instantiateCandidate(candFun.get(dp.rhs().queryRoot()), dp.rhs()).toString();
      if (indexOfOrientedDPs.contains(index)) {
        Informal.getInstance().addProofStep("  " + dp.constraint().toString() + " ⊨ " + left +
          " > " + right + " (and " + left + "≥ 0)    for the DP " + dp.toString());
      }
      else {
        Informal.getInstance().addProofStep("  " + dp.constraint().toString() + " ⊨ " + left +
          " ≥ " + right + "    for the DP " + dp.toString());
      }
    }
    Informal.getInstance().addProofStep("And we remove all strictly oriented DPs.");

    GraphProcessor gProc = new GraphProcessor();
    return gProc.processDPP(new Problem(remainingDPs, dpp.getTRS()));
  }
}
