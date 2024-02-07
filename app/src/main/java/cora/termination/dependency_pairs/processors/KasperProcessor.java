package cora.termination.dependency_pairs.processors;

import cora.smt.*;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;
import cora.terms.*;

import java.util.*;
import java.util.function.Consumer;

public class KasperProcessor implements Processor {

  private final SmtProblem _smt = new SmtProblem();

  private Map< FunctionSymbol, List<Variable> > _fnToFreshVar;

  private Map< FunctionSymbol, List<Term> > _candidates;

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

    Map<FunctionSymbol, List<Variable>> ret = new TreeMap<>();
    allSharps
      .forEach( fSharp -> {
        List<Variable> newVars = DPGenerator.generateVars(fSharp.queryType());
        ret.put(fSharp, newVars);
      });

    return ret;
  }

  private Map<FunctionSymbol, List<Term>> computeInitialCandidates(Problem dpp) {
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
   * Updates the
   * @param dpp
   * @return
   */
  private void updateCandidates(Problem dpp) {
    for(DP dp : dpp.getDPList()) {

      System.out.println("The DP we are updating the candidates is: " + dp);

      // Decomposition of this dp as lhs => rhs [ ctr | V ]
      Term lhs = dp.lhs();
      Term rhs = dp.rhs();
      Term ctr = dp.constraint();
      List<Variable> V = dp.vars();

      // Given f# s1 ... sn (being the lhs or rhs of a DP), the consumer handler
      // should do the following:
      // for each si in [s1, ..., sn]
      //     if si is not a theory term or vars(si) contains some variable not in V then:
      //         we remove from _candidates(f#) all terms u such that the corresponding freshly generated variable
      //         in _fnToFreshVar(f#) xi belongs to vars(u).
      Consumer<Term> handler = (
        s -> {
          System.out.println("The term is : " + s);
          for (Term si : s.queryArguments()) {
            boolean siVarTest = false;
            for (Variable v : si.vars()) {
              if (V.contains(v)) { continue; } else { siVarTest = true; break;}
            }
            if(!si.isTheoryTerm() || siVarTest) {
              FunctionSymbol fSharp = s.queryRoot();
              Variable xi = _fnToFreshVar.get(fSharp).get(s.queryArguments().indexOf(si));
              System.out.println("Analysing " + fSharp + " at argument " + si + ", which should be removed.");

              System.out.println("Initial candidates " + _candidates.get(fSharp));

              List<Term> updatedCandidates = _candidates.get(fSharp)
                .stream()
                .filter(t -> !t.vars().contains(xi))
                .toList();
              _candidates.replace(fSharp, updatedCandidates);

              System.out.println("Updated candidates: " + updatedCandidates);

              System.out.println("Moving to next argument...\n\n\n");

            }
          }
        }
      );
      handler.accept(lhs);
      System.out.println("------------------------------------");
      handler.accept(rhs);
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
      int upperBound = _candidates.get(f).size();
      _smt.require(SmtProblem.createLeq(SmtProblem.createValue(1), ivar));
      _smt.require(SmtProblem.createLeq(ivar, SmtProblem.createValue(upperBound)));
    });
  }

  private void requireAtLeastOneStrict(Map<DP, BVar> boolMap) {
    ArrayList<Constraint> disj = new ArrayList<Constraint>();
    for (BVar b : boolMap.values()) {
      disj.add(b);
    }
    _smt.require(SmtProblem.createDisjunction(disj));
  }

  private void putDpRequirements(Map<FunctionSymbol, IVar> intMap, Map<DP, BVar> boolMap, Problem dpp) {
    for (DP dp : dpp.getDPList()) {
      Term lhs = dp.lhs();
      Term rhs = dp.rhs();
      Term ctr = dp.constraint();

      FunctionSymbol lhsHead = lhs.queryRoot();
      FunctionSymbol rhsHead = rhs.queryRoot();

      for(int i = 0; i < _candidates.get(lhsHead).size(); i++) {
        for(int j = 0; j < _candidates.get(rhsHead).size(); j++) {

          Term candLi = _candidates.get(lhsHead).get(i);
          Term candRj = _candidates.get(rhsHead).get(j);

          Substitution substL = TermFactory.createEmptySubstitution();
          Substitution substR = TermFactory.createEmptySubstitution();

          for(int varL = 0; varL < lhsHead.queryArity(); varL ++) {
            substL.extend(_fnToFreshVar.get(lhsHead).get(varL), lhs.queryArgument(varL + 1));
          }
          for(int varR = 0; varR < rhsHead.queryArity(); varR ++) {
            substR.extend(_fnToFreshVar.get(rhsHead).get(varR), rhs.queryArgument(varR + 1));
          }

          SmtProblem validityProblem = new SmtProblem();

          Constraint constraintTranslation =
            TermSmtTranslator.translateConstraint(ctr, validityProblem);

          IntegerExpression candLiExpr =
            TermSmtTranslator.
              translateIntegerExpression(candLi.substitute(substL), validityProblem);
          IntegerExpression candRjExpr =
            TermSmtTranslator.
              translateIntegerExpression(candRj.substitute(substR), validityProblem);

          validityProblem
            .requireImplication(constraintTranslation, SmtProblem.createGeq(candLiExpr, candRjExpr));

          //Of and Og constraints
          Constraint fSharpDisjunction =
            SmtProblem.createDisjunction (
              SmtProblem.createUnequal(intMap.get(lhsHead), SmtProblem.createValue(i)),
              SmtProblem.createUnequal(intMap.get(rhsHead), SmtProblem.createValue(j))
            );

          if(validityProblem.isValid()) {

            validityProblem.clear();

            validityProblem.requireImplication (
              constraintTranslation,
              SmtProblem.createConjunction (
                SmtProblem.createGeq(candLiExpr, SmtProblem.createValue(0)),
                SmtProblem.createGreater(candLiExpr, candRjExpr)
              ));

            if(validityProblem.isValid()) {
              continue;
            } else {
              _smt.require (
                SmtProblem.createDisjunction(
                  fSharpDisjunction,
                  SmtProblem.createNegation(boolMap.get(dp))
                ));
            }

          } else {
            _smt.require(fSharpDisjunction);
          }
        }
      }
    }
    System.out.println("The analysis for all DPs done, here's the SMT state: " + _smt);
  }

  @Override
  public Optional<List<Problem>> processDPP(Problem dpp) {

    _fnToFreshVar = computeFreshVars(dpp);

    System.out.println("\n\n\nCompletely fresh vars : " + _fnToFreshVar);

    _candidates = computeInitialCandidates(dpp);

    updateCandidates(dpp);

    System.out.println("------- testing generation of constraints\n");
    Map<FunctionSymbol, IVar> intMap = generateIVars(dpp);
    requiresCtrs(intMap);
    Map<DP, BVar> boolMap = generateDpBVarMap(dpp);
    requireAtLeastOneStrict(boolMap);
    putDpRequirements(intMap, boolMap, dpp);

    Valuation result = _smt.satisfy();

    if(result == null) {
      System.out.println("No solution found");
    } else {
      System.out.println("The value of boolMap for each DP");
      boolMap.forEach(
        (dp, ibool) -> {
          System.out.println("For the DP " + dp + " I found the value " + result.queryAssignment(ibool));
        }
      );
      System.out.println("The value of intMap for all f# in the Problem: ");
      intMap.forEach(
        (fSharp, iint) -> {
          System.out.println("For the sharp symbol " + fSharp + " I found the value " + result.queryAssignment(iint));
          System.out.println("J(" + fSharp + ") = " + _candidates.get(fSharp).get(result.queryAssignment(iint)-1));
        }
      );
    }


    return null;
  }
}
