/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.termination.dependency_pairs.processors;

import java.util.*;
import java.util.function.Consumer;

import charlie.types.*;
import charlie.terms.*;
import charlie.smt.*;
import charlie.trs.TrsProperties.*;
import charlie.theorytranslation.TermSmtTranslator;
import cora.io.OutputModule;
import cora.config.Settings;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;

public class IntegerMappingProcessor implements Processor {

  private SmtProblem _smt;
  private Map< FunctionSymbol, List<Variable> > _fnToFreshVar;
  private Map< FunctionSymbol, List<Term> > _candidates;

  /** This technique can be disabled by runtime arguments. */
  public static String queryDisabledCode() { return "imap"; }

  @Override
  public boolean isApplicable(Problem dp) {
    return !Settings.isDisabled(queryDisabledCode()) &&
           dp.getOriginalTRS().verifyProperties(Level.APPLICATIVE, Constrained.YES,
                                                Products.DISALLOWED, Lhs.PATTERN, Root.THEORY);
  }

  /**
   * For a DPP problem {@code dpp}, returns a mapping of each f# : A1 ⇒ ... ⇒ An ⇒ DP_SORT
   * in heads(P) to the list of fresh variables [x1 : A1, ..., xn : An].
   */
  private Map<FunctionSymbol, List<Variable>> computeFreshVars(Problem dpp) {
    Set<FunctionSymbol> allSharps = dpp.getHeads();

    Map<FunctionSymbol, List<Variable>> ret = new TreeMap<>();
    allSharps
      .forEach( fSharp -> {
        Type ty = fSharp.queryType();
        ArrayList<Variable> newvars = new ArrayList<Variable>();
        for (int i = 1; ty instanceof Arrow(Type left, Type right); i++) {
          newvars.add(TermFactory.createVar("arg_" + i, left));
          ty = right;
        }
        ret.put(fSharp, newvars);
      });

    return ret;
  }

  private Term makePlus(Term a, Term b) {
    return TermFactory.createApp(TheoryFactory.plusSymbol, a, b);
  }

  /** This creates an empty set of candidates for every root symbol of interest. */
  private void initiateCandidates(Problem dpp) {
    Set<FunctionSymbol> allSharps = dpp.getHeads();
    _candidates = new TreeMap<FunctionSymbol,List<Term>>();
    allSharps.forEach(fSharp -> {
      _candidates.put(fSharp, new ArrayList<Term>());
    });
  }

  /** This computes all candidates of the form arg_i and arg_i - 1, where the ith argument is of theory sort. */
  private void addSimpleCandidates() {
    _candidates.forEach( (fSharp, options) -> {
      for (Variable y : _fnToFreshVar.get(fSharp).stream()
                        .filter(x -> x.queryType().equals(TypeFactory.intSort))
                        .toList()) {
        options.add(y);
        options.add(makePlus(y, TheoryFactory.createValue(-1)));
        options.add(makePlus(y, TheoryFactory.createValue(1)));
      }
    });
  }

  /** This computes all candidates based on the constraints of a dependency pair. */
  private void addComplexCandidates(Problem dpp) {
    for (DP dp : dpp.getDPList()) {
      Term lhs = dp.lhs();
      Term root = lhs.queryRoot();
      // let subst be the substitution such that, if left = f l1 ... ln and li is a variable of
      // theory sort, then subst[li] = x_i^f
      Substitution subst = TermFactory.createEmptySubstitution();
      for (int i = 1; i <= lhs.numberArguments(); i++) {
        Term argi = lhs.queryArgument(i);
        if (argi.isVariable() && argi.queryType().isTheoryType() && argi.queryType().isBaseType()) {
          subst.extend(argi.queryVariable(), _fnToFreshVar.get(root).get(i-1));
        }
      }
      // let suggestions be the suggestions obtained from comparisons in the constraint, but not
      // yet adapted with the argument variables
      ArrayList<Term> suggestions = new ArrayList<Term>();
      addAllComparisonFunctions(dp.constraint(), suggestions);
      // filter out those that use variables we aren't allowed to use, and store the remainder in
      // candidates!
      for (Term s : suggestions) {
        boolean ok = true;
        for (Variable x : s.vars()) {
          if (subst.get(x) == null) { ok = false; break; }
        }
        if (ok) _candidates.get(root).add(s.substitute(subst));
      }
    }
  }

  /**
   * Given a constraint, for all comparisons s ≥ t that occur in it (below ∧ or ∨), add s - t to
   * ret.  This includes other comparisons that can be seen as a ≥; for instance if s < t occurs
   * then we add t - s - 1.
   */
  private void addAllComparisonFunctions(Term constraint, ArrayList<Term> ret) {
    if (!constraint.isFunctionalTerm()) return;
    FunctionSymbol f = constraint.queryRoot();
    if (f.equals(TheoryFactory.andSymbol) || f.equals(TheoryFactory.orSymbol)) {
      for (int i = 1; i <= constraint.numberArguments(); i++) {
        addAllComparisonFunctions(constraint.queryArgument(i), ret);
      }
    }
    if (constraint.numberArguments() != 2) return;
    Term left = constraint.queryArgument(1);
    Term right = constraint.queryArgument(2);
    // left ≥ right  =>  left - right
    if (f.equals(TheoryFactory.geqSymbol) || f.equals(TheoryFactory.intEqualSymbol) ||
        f.equals(TheoryFactory.greaterSymbol)) {
      if (right.equals(TheoryFactory.createValue(0))) ret.add(left);
      else {
        Term minright = TheoryFactory.minusSymbol.apply(right);
        ret.add(makePlus(left, minright));
      }
    }
    // left > right  =>  left - right - 1
    if (f.equals(TheoryFactory.greaterSymbol)) {
      Term minright = TheoryFactory.minusSymbol.apply(right);
      Term leftminright = makePlus(left, minright);
      if (right.equals(TheoryFactory.createValue(0))) leftminright = left;
      Term minone = TheoryFactory.createValue(-1);
      ret.add(makePlus(leftminright, minone));
    }
    // left ≤ right  =>  right - left
    if (f.equals(TheoryFactory.leqSymbol) || f.equals(TheoryFactory.intEqualSymbol) ||
        f.equals(TheoryFactory.smallerSymbol)) {
      if (left.equals(TheoryFactory.createValue(0))) ret.add(right);
      else {
        Term minleft = TheoryFactory.minusSymbol.apply(left);
        ret.add(makePlus(right, minleft));
      }
    }
    // left < right  =>  right - left - 1
    if (f.equals(TheoryFactory.smallerSymbol)) {
      Term minleft = TheoryFactory.minusSymbol.apply(left);
      Term rightminleft = makePlus(right, minleft);
      if (left.equals(TheoryFactory.createValue(0))) rightminleft = right;
      Term minone = TheoryFactory.createValue(-1);
      ret.add(makePlus(rightminleft, minone));
    }
  }

  private boolean everyFunctionHasAtLeastOneCandidate() {
    for (List<Term> xs : _candidates.values()) {
      if (xs.size() == 0) return false;
    }
    return true;
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
  private void filterCandidateList(Term term, Set<Variable> theoryVars) {
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
    for (DP dp : dpp.getDPList()) {

      // Decomposition of this dp as lhs => rhs [ ctr | V ]
      Term lhs = dp.lhs();
      Term rhs = dp.rhs();
      Term ctr = dp.constraint();
      Set<Variable> V = dp.lvars();

      filterCandidateList(lhs, V);
      filterCandidateList(rhs, V);
    }
  }

  private Map<FunctionSymbol, IVar> generateIVars(Problem dpp) {
    Set<FunctionSymbol> allFns = dpp.getHeads();
    Map<FunctionSymbol, IVar> retMap = new TreeMap<>();

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
      _smt.require(SmtFactory.createLeq(SmtFactory.createValue(0), ivar));
      _smt.require(SmtFactory.createLeq(ivar, SmtFactory.createValue(upperBound)));
    });
  }

  private void requireAtLeastOneStrict(Map<DP, BVar> boolMap) {
    ArrayList<Constraint> disj = new ArrayList<Constraint>();
    for (BVar b : boolMap.values()) disj.add(b);
    _smt.require(SmtFactory.createDisjunction(disj));
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
          TermSmtTranslator tst = new TermSmtTranslator(validityProblem);

          // translate the constraint and instantiated candidates to smt language
          Constraint constraintTranslation = tst.translateConstraint(ctr);
          IntegerExpression candLiExpr = tst.translateIntegerExpression(instLi);
          IntegerExpression candRjExpr = tst.translateIntegerExpression(instRj);
          
          // fSharpDisjunction = nu(leftroot) != i \/ nu(rightroot) != j
          Constraint fSharpDisjunction =
            SmtFactory.createDisjunction (
              SmtFactory.createUnequal(intMap.get(lhsHead), SmtFactory.createValue(i)),
              SmtFactory.createUnequal(intMap.get(rhsHead), SmtFactory.createValue(j))
            );

          // check one: if left ≥ right doesn't even hold, then we can't have that choice of
          // candidates
          validityProblem
            .requireImplication(constraintTranslation, SmtFactory.createGeq(candLiExpr, candRjExpr));
          if (!Settings.smtSolver.checkValidity(validityProblem)) {
            _smt.require(fSharpDisjunction);
            continue;
          }

          // check two: if left > right holds, then having this choice of candidates means that the
          // DP is oriented strictly; if it doesn't, then it means the DP is not oriented strictly
          validityProblem.clear();
          validityProblem.requireImplication (
            constraintTranslation,
            SmtFactory.createConjunction (
              SmtFactory.createGeq(candLiExpr, SmtFactory.createValue(0)),
              SmtFactory.createGreater(candLiExpr, candRjExpr)
            ));

          if (Settings.smtSolver.checkValidity(validityProblem)) {
            _smt.require(
              SmtFactory.createDisjunction(
                fSharpDisjunction,
                boolMap.get(dp)
              ));
          } else {
            _smt.require (
              SmtFactory.createDisjunction(
                fSharpDisjunction,
                SmtFactory.createNegation(boolMap.get(dp))
              ));
          }
        }
      }
    }
  }

  @Override
  public IntegerMappingProof processDPP(Problem dpp) {
    _smt = new SmtProblem();

    _fnToFreshVar = computeFreshVars(dpp);

    initiateCandidates(dpp);
    addSimpleCandidates();
    addComplexCandidates(dpp);
    updateCandidates(dpp);
    if (!everyFunctionHasAtLeastOneCandidate()) return new IntegerMappingProof(dpp);

    Map<FunctionSymbol, IVar> intMap = generateIVars(dpp);
    requiresCtrs(intMap);
    Map<DP, BVar> boolMap = generateDpBVarMap(dpp);
    requireAtLeastOneStrict(boolMap);
    putDpRequirements(intMap, boolMap, dpp);

    Valuation result = switch (Settings.smtSolver.checkSatisfiability(_smt)) {
      case SmtSolver.Answer.YES(Valuation val) -> val;
      default -> null;
    };

    if (result == null) return new IntegerMappingProof(dpp);

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

    return new IntegerMappingProof(dpp, indexOfOrientedDPs, _fnToFreshVar, candFun);
  }
}

