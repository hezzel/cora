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

package cora.termination.reduction_pairs.horpo;

import charlie.util.Pair;
import charlie.types.*;
import charlie.terms.*;
import charlie.trs.TrsProperties.*;
import charlie.smt.*;
import charlie.theorytranslation.TermSmtTranslator;
import cora.config.Settings;
import cora.termination.reduction_pairs.*;
import cora.termination.reduction_pairs.horpo.HorpoConstraintList.HRelation;
import cora.termination.reduction_pairs.horpo.HorpoConstraintList.HorpoRequirement;

import java.util.List;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

public class Horpo implements ReductionPair {
  /** This technique can be disabled by runtime arguments. */
  public static String queryDisabledCode() { return "horpo"; }

  /** Checks that the given ordering problem satisfies the requirements to try and apply HORPO */
  public boolean isApplicable(OrderingProblem prob) {
    return !Settings.isDisabled(queryDisabledCode()) &&
           prob.queryOriginalTRS().verifyProperties(Level.APPLICATIVE, Constrained.YES,
                                                    Products.DISALLOWED, Lhs.NONPATTERN, Root.ANY);
  }

  /** Main access function: start a HORPO proof to generate a suitable reduction pair. */
  public ReductionPairProofObject solve(OrderingProblem problem, SmtProblem smt) {
    int bound = computeIntegerVariableBound(problem);
    HorpoParameters param = new HorpoParameters(bound, smt);
    TreeSet<String> avoid = getFunctionSymbols(problem);
    TermPrinter printer = new TermPrinter(avoid);
    HorpoConstraintList lst = new HorpoConstraintList(printer, smt);
    TreeMap<Integer,BVar> choices = setupConstraintList(lst, problem, smt);
    Monotonicity mono = problem.queryMonotonicity();
    HorpoSimplifier simplifier = new HorpoSimplifier(param, lst, mono);
    for (int i = 0; i < lst.size(); i++) simplifier.simplify(lst.get(i));
    return finish(problem, choices, param, lst);
  }

  /** Stores the left-hand side, right-hand side and constraint of req into terms. */
  private void addTerms(LinkedList<Term> terms, OrderingRequirement req) {
    terms.add(req.left());
    terms.add(req.right());
    terms.add(req.constraint());
  }

  /** Returns a list with all left-hand sides, right-hand sides and constraints in problem */
  private LinkedList<Term> getAllTerms(OrderingProblem problem) {
    LinkedList<Term> ret = new LinkedList<Term>();
    for (OrderingRequirement r : problem.unconditionalReqs()) addTerms(ret, r);
    for (Pair<Constraint,OrderingRequirement> p : problem.conditionalReqs()) addTerms(ret, p.snd());
    for (Pair<Integer,OrderingRequirement> p : problem.eitherReqs()) addTerms(ret, p.snd());
    return ret;
  }

  /**
   * Helper class for computeIntegerVariableBound.  This is needed because local variables used in
   * a lambda-expression must be effectively final, so it is necessary to wrap our very much
   * non-final variable in a class.
   */
  private class IntWrapper { int num; IntWrapper(int n) { num = n; } }

  /**
   * Returns twice the largest integer value occurring in the given OrderingProblem, or 1000 if
   * that is bigger.
   */
  private int computeIntegerVariableBound(OrderingProblem problem) {
    IntWrapper wrapper = new IntWrapper(500);
    for (Term term : getAllTerms(problem)) {
      term.visitSubterms( (s,p) -> {
        if (s.isValue() && s.queryType().equals(TypeFactory.intSort)) {
          Value value = s.toValue();
          if (value.getInt() > wrapper.num) wrapper.num = value.getInt();
          if (- value.getInt() > wrapper.num) wrapper.num = - value.getInt();
        }
      });
    }
    return wrapper.num * 2;
  }

  /** Returns a set with all the function symbols occurring in the given problem. */
  private TreeSet<String> getFunctionSymbols(OrderingProblem problem) {
    TreeSet<FunctionSymbol> symbs = new TreeSet<FunctionSymbol>();
    for (Term term : getAllTerms(problem)) term.storeFunctionSymbols(symbs);
    TreeSet<String> ret = new TreeSet<String>();
    for (FunctionSymbol f : symbs) ret.add(f.queryName());
    return ret;
  }

  /**
   * This function adds the requirements of the given ordering problem into the given Horpo
   * Constraint list.  It also adds clauses to the given SMT problem that together ensure that the
   * ordering problem is satisfied if the SMT problem is satisfied by a valuation where the
   * defining variables of the Horpo requirements truly represent the truth of these requirements.
   *
   * The return value lists, for each identifier of an "either" requirement in the ordering problem,
   * a BVar that represents that the requirement was oriented strictly.
   */
  private TreeMap<Integer,BVar> setupConstraintList(HorpoConstraintList lst,
                                                    OrderingProblem problem,
                                                    SmtProblem smt) {
    BVar x;
    // unconditional requirements: these should all be satisfied
    for (OrderingRequirement req : problem.unconditionalReqs()) {
      HRelation rel = switch (req.rel()) {
        case OrderingRequirement.Relation.Strict -> HRelation.GREATER;
        case OrderingRequirement.Relation.Weak -> HRelation.GEQ;
      };
      x = lst.store(req.left(), rel, req.right(), req.constraint(), req.tvar());
      smt.require(x);
    }
    // conditional requirements: these should be satisfied if their underlying constraint is
    for (Pair<Constraint,OrderingRequirement> p : problem.conditionalReqs()) {
      OrderingRequirement req = p.snd();
      HRelation rel = switch (req.rel()) {
        case OrderingRequirement.Relation.Strict -> HRelation.GREATER;
        case OrderingRequirement.Relation.Weak -> HRelation.GEQ;
      };
      x = lst.store(req.left(), rel, req.right(), req.constraint(), req.tvar());
      smt.requireImplication(p.fst(), x);
    }
    // either requirements: if non-empty, at least one of these should be satisfied
    TreeMap<Integer,BVar> ret = new TreeMap<Integer,BVar>();
    if (problem.eitherReqs().isEmpty()) return ret;
    LinkedList<Constraint> oneof = new LinkedList<Constraint>();
    for (Pair<Integer,OrderingRequirement> p : problem.eitherReqs()) {
      OrderingRequirement req = p.snd();
      x = lst.store(req.left(), HRelation.GREATER, req.right(), req.constraint(), req.tvar());
      BVar y = lst.store(req.left(), HRelation.GEQNOGR, req.right(), req.constraint(), req.tvar());
      smt.require(SmtFactory.createDisjunction(x, y));
      oneof.add(x);
      ret.put(p.fst(), x);
    }
    smt.require(SmtFactory.createDisjunction(oneof));
    return ret;
  }

  /**
   * This function serves to finish up: once the constraint list has been simplified, we ask the
   * SmtSolver to solve the resulting SMT problem, and we generate a HorpoResult for that.
   */
  private HorpoResult finish(OrderingProblem orderingProblem, TreeMap<Integer,BVar> choices,
                             HorpoParameters param, HorpoConstraintList lst) {
    Valuation valuation = null;
    switch (Settings.smtSolver.checkSatisfiability(param.queryProblem())) {
      case SmtSolver.Answer.YES(Valuation val): valuation = val; break;
      default:  // no solution => let's return a MAYBE
        return new HorpoResult(orderingProblem, "Could not find a HORPO proof.");
    };
    TreeSet<Integer> strict = new TreeSet<Integer>();
    for (Map.Entry<Integer,BVar> entry : choices.entrySet()) {
      BVar x = entry.getValue();
      if (valuation.queryBoolAssignment(x.queryIndex())) strict.add(entry.getKey());
    }
    TreeSet<Integer> conditions = new TreeSet<Integer>();
    List< Pair<Constraint,OrderingRequirement> > creqs = orderingProblem.conditionalReqs();
    for (int i = 0; i < creqs.size(); i++) {
      if (creqs.get(i).fst().evaluate(valuation)) conditions.add(i);
    }
    return new HorpoResult(orderingProblem, strict, conditions, valuation, param, lst);
  }
}
