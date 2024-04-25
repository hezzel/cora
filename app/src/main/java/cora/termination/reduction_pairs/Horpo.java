/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.termination.reduction_pairs;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Map;
import charlie.types.*;
import charlie.terms.*;
import charlie.smt.*;
import charlie.trs.*;
import charlie.trs.TrsProperties.*;
import charlie.theorytranslation.TermSmtTranslator;
import cora.config.Settings;

/** This is an implementation of a basic version of Horpo for LCSTRSs (so with constraints). */
public class Horpo {
  private boolean _strict;

  /** This technique can be disabled by runtime arguments. */
  public static String queryDisabledCode() { return "horpo"; }

  /**
   * This function returns whether this reduction pair can be applied to the given TRS at all.
   * This is the case if it's an LCSTRS: an applicative constrained system where left-hand sides
   * are not theory terms.
   */
  public static boolean applicable(TRS trs) {
    return !Settings.isDisabled(queryDisabledCode()) &&
           trs.verifyProperties(Level.APPLICATIVE, Constrained.YES, Products.DISALLOWED,
                                Lhs.NONPATTERN, Root.ANY);
  }

  /**
   * Given a TRS, this checks if it can be proved terminating using Horpo, and if so, returns a
   * HorpoResult describing the Horpo proof.  If not, a HorpoResult describing failure is returned
   * instead.  (In this case the termination couldn't be proved; we cannot conclude non-termination
   * from this.)
   */
  public static HorpoResult proveTermination(TRS trs) {
    OrderingProblem problem = OrderingProblem.createStrictProblem(trs);
    if (!applicable(trs)) {
      return new HorpoResult(problem,
                             "The current implementation of HORPO can only be applied on " +
                             "systems with applicative term formation and no tuples.");
    }
    Horpo horpo = new Horpo(true);
    return horpo.orient(problem);
  }

  /**
   * Constructor: sets up Horpo either as a strongly monotonic reduction pair, or as a weakly
   * monotonic reduction pair.
   */
  public Horpo(boolean strict) {
    _strict = strict;
  }

  /**
   * The main reduction pair access function.  Tries to orient the given OrderingProblem, and
   * returns a proof object to represent the result of this attempt.
   */
  public HorpoResult orient(OrderingProblem problem) {
    int bound = computeIntegerVariableBound(problem);
    HorpoParameters param = new HorpoParameters(bound, _strict);
    TreeSet<String> avoid = getFunctionSymbols(problem);
    TermPrinter printer = new TermPrinter(avoid);
    HorpoConstraintList lst = new HorpoConstraintList(param, printer);
    TreeMap<Integer,BVar> choices = setupConstraintList(lst, param.queryProblem(), problem);
    while (!lst.isFullySimplified()) lst.simplify();
    return solve(problem, choices, param, lst);
  }

  /**
   * Returns twice the largest integer value occurring in the given OrderingProblem, or 1000 if
   * that is bigger.
   */
  private int computeIntegerVariableBound(OrderingProblem problem) {
    int ret = 500;
    LinkedList<Term> parts = new LinkedList<Term>();
    for (OrderingRequirement req : problem.reqs()) {
      parts.push(req.left());
      parts.push(req.right());
      parts.push(req.constraint());
    }
    while (!parts.isEmpty()) {
      Term part = parts.pop();
      if (part.isValue() && part.queryType().equals(TypeFactory.intSort)) {
        Value value = part.toValue();
        if (value.getInt() > ret) ret = value.getInt();
        if (- value.getInt() > ret) ret = - value.getInt();
      }
      if (part.isApplication()) {
        for (int i = 1; i <= part.numberArguments(); i++) parts.push(part.queryArgument(i));
      }
    }
    return ret * 2;
  }

  /** Returns a set with all the function symbols occurring in the given problem. */
  private TreeSet<String> getFunctionSymbols(OrderingProblem problem) {
    TreeSet<FunctionSymbol> symbs = new TreeSet<FunctionSymbol>();
    for (OrderingRequirement req : problem.reqs()) {
      req.left().storeFunctionSymbols(symbs);
      req.right().storeFunctionSymbols(symbs);
      req.constraint().storeFunctionSymbols(symbs);
    }
    TreeSet<String> ret = new TreeSet<String>();
    for (FunctionSymbol f : symbs) ret.add(f.queryName());
    return ret;
  }

  /**
   * This function adds the requirements of the given list into the given ordering problem,
   * adds clauses to the requirement to ensure that the ordering problem is satisfied, and returns
   * a map that indicates, for each EITHER entry in the ordering problem, the BVar that will
   * eventually indicate if it is ordered strictly.
   */
  private TreeMap<Integer,BVar> setupConstraintList(HorpoConstraintList lst, SmtProblem sprob,
                                                    OrderingProblem problem) {
    TreeMap<Integer,BVar> ret = new TreeMap<Integer,BVar>();
    for (int i = 0; i < problem.reqs().size(); i++) {
      OrderingRequirement req = problem.reqs().get(i);
      BVar bvar;
      switch (req.rel()) {
        case OrderingRequirement.Relation.Strict:
          BVar z = lst.store(req.left(), HorpoConstraintList.StartRelation.Greater,
                             req.right(), req.constraint(), req.tvar());
          sprob.require(z);
          ret.put(i, z);
          break;
        case OrderingRequirement.Relation.Weak:
          sprob.require(lst.store(req.left(), HorpoConstraintList.StartRelation.Geq,
                        req.right(), req.constraint(), req.tvar()));
          break;
        case OrderingRequirement.Relation.Either:
          BVar x = lst.store(req.left(), HorpoConstraintList.StartRelation.Greater, req.right(),
                             req.constraint(), req.tvar());
          BVar y = lst.store(req.left(), HorpoConstraintList.StartRelation.GeqNoGr, req.right(),
                             req.constraint(), req.tvar());
          sprob.require(SmtFactory.createDisjunction(x, y));
          ret.put(i, x);
          break;
      }
    }
    return ret;
  }

  /**
   * This function serves to finish up: once the constraint list has been simplified, we ask the
   * SmtSolver to solve the resulting SMT problem, and we generate a HorpoResult for that.
   */
  private HorpoResult solve(OrderingProblem orderingProblem, TreeMap<Integer,BVar> choices,
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
    return new HorpoResult(orderingProblem, strict, valuation, param, lst);
  }
}

