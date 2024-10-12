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

import java.util.*;

/**
 * This class represents an implementation of Constrained Horpo: the question whether s! ≻ t! or
 * s! ≽ t!, where u! represents the normal form of u with respect to only the calculation rules.
 * We fix values to be minimal with respect to the precedence.
 * For now, we do not yet support the f* mechanism, meta-variables, tuples or abstractions, but
 * these are planned to be included in the future.
 */
public class Horpo implements ReductionPair {
  private boolean _strong;

  /**
   * When given true, creates a strongly monotonic constrained reduction pair based on the higher
   * order recursive path ordering.  When given false, creates a weakly monotonic reduction pair.
   */
  public Horpo(boolean stronglyMonotonic) {
    _strong = stronglyMonotonic;
  }

  /** This technique can be disabled by runtime arguments. */
  public static String queryDisabledCode() { return "horpo"; }

  /** Returns whether this Horpo instance is strongly monotonic */
  public boolean isStronglyMonotonic() { return _strong; }

  /** Checks that the given ordering problem satisfies the requirements to try and apply HORPO */
  public boolean isApplicable(OrderingProblem prob) {
    return !Settings.isDisabled(queryDisabledCode()) &&
           prob.queryOriginalTRS().verifyProperties(Level.APPLICATIVE, Constrained.YES,
                                                    Products.DISALLOWED, Lhs.NONPATTERN, Root.ANY);
  }

  /** Returns a short description of what this reduction pair is. */
  public String queryName() {
    if (_strong) return "strict-HORPO";
    else return "HORPO";
  }

  /** Returns the name of this reduction pair */
  public String toString() {
    return queryName();
  }

  /** Main access function: start a HORPO proof to generate a suitable reduction pair. */
  public ReductionPairProofObject solve(OrderingProblem problem, SmtProblem smt) {
    int bound = computeIntegerVariableBound(problem);
    TreeSet<FunctionSymbol> symbols = getFunctionSymbols(problem);
    ArgumentFilter filter = problem.queryArgumentFilter();
    HorpoParameters param = new HorpoParameters(bound, symbols, filter, smt);
    TermPrinter printer = new TermPrinter(getFunctionSymbolNames(symbols));
    HorpoConstraintList lst = new HorpoConstraintList(printer, smt);
    TreeMap<Integer,BVar> choices = setupConstraintList(lst, problem, smt);
    // for Horpo, strong monotonicity just means regarding all arguments
    if (_strong) filter.forceEmpty();
    HorpoSimplifier simplifier = new HorpoSimplifier(param, lst, filter);
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
   * Returns a list with all left-hand and right-hand sides in constraints in problem, each coupled
   * with the corresponding set of theory variables.
   */
  private LinkedList<Pair<Term,Set<Variable>>> getSideTerms(OrderingProblem problem) {
    LinkedList<Pair<Term,Set<Variable>>> ret = new LinkedList<Pair<Term,Set<Variable>>>();
    for (OrderingRequirement req : problem.unconditionalReqs()) {
      ret.add(new Pair<Term,Set<Variable>>(req.left(), req.tvar()));
      ret.add(new Pair<Term,Set<Variable>>(req.right(), req.tvar()));
    }
    for (Pair<Constraint,OrderingRequirement> p : problem.conditionalReqs()) {
      OrderingRequirement req = p.snd();
      ret.add(new Pair<Term,Set<Variable>>(req.left(), req.tvar()));
      ret.add(new Pair<Term,Set<Variable>>(req.right(), req.tvar()));
    }
    for (Pair<Integer,OrderingRequirement> p : problem.eitherReqs()) {
      OrderingRequirement req = p.snd();
      ret.add(new Pair<Term,Set<Variable>>(req.left(), req.tvar()));
      ret.add(new Pair<Term,Set<Variable>>(req.right(), req.tvar()));
    }
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

  /**
   * Returns a set with all the function symbols occurring in the given problem, not including
   * any symbol in a base-type theory term whose variables are all in tvar.
   */
  private TreeSet<FunctionSymbol> getFunctionSymbols(OrderingProblem problem) {
    LinkedList<Pair<Term,Set<Variable>>> relevant = getSideTerms(problem);
    TreeSet<FunctionSymbol> symbs = new TreeSet<FunctionSymbol>();
    for (Pair<Term,Set<Variable>> p : relevant) {
      Set<Variable> set = p.snd();
      p.fst().visitSubterms( (s,pos) -> {
        if (s.isFunctionalTerm()) {
          if (s.isTheoryTerm() && s.queryType().isBaseType()) {
            for (Variable x : s.vars()) {
              if (!set.contains(x)) { symbs.add(s.queryRoot()); break; }
            }
          }
          else symbs.add(s.queryRoot());
        }
      } );
    }
    return symbs;
  }

  /** Returns a set with all the function symbol names occuring in the given set. */
  private TreeSet<String> getFunctionSymbolNames(TreeSet<FunctionSymbol> symbols) {
    TreeSet<String> ret = new TreeSet<String>();
    for (FunctionSymbol f : symbols) ret.add(f.queryName());
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
        return new HorpoResult(orderingProblem, "No HORPO proof could be found.");
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
