package cora.termination.dependency_pairs.processors;

import cora.terms.*;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import java.util.Optional;
import java.util.ArrayList;

import java.util.*;

public class SplittingProcessor implements Processor {
  @Override
  public boolean isApplicable(Problem dp) { return true; }
  
  /**
   * For C1 o...o Cn, where Ci does not have o as a root symbol, this appends [C1,...,Cn] to sofar.
   * (This is intended to be used for associative operators, specifically /\ and \/.)
   */
  private void addJunctionParts(Term constraint, FunctionSymbol root, ArrayList<Term> sofar) {
    if (!constraint.isFunctionalTerm()) sofar.add(constraint);
    else if (!constraint.queryRoot().equals(root)) sofar.add(constraint);
    else {
      for (int i = 1; i <= constraint.numberArguments(); i++) {
        addJunctionParts(constraint.queryArgument(i), root, sofar);
      }
    }
  }

  /** For C1 /\.../\ Cn, where Ci is not a conjunction, this returns the list [C1,...,Cn] */
  private ArrayList<Term> getConjunctionComponents(Term constraint) {
    ArrayList<Term> ret = new ArrayList<Term>();
    addJunctionParts(constraint, TheoryFactory.andSymbol, ret);
    return ret;
  }

  /**
   * If this term is a != b, returns [a < b, a > b].
   * If this term is a1 \/ ... \/ an, returns [a1,...,an].
   * Otherwise, returns empty.
   */
  private Optional<ArrayList<Term>> split(Term constraint) {
    if (!constraint.isFunctionalTerm()) return Optional.empty();
    if (constraint.queryRoot().equals(TheoryFactory.distinctSymbol) &&
        constraint.numberArguments() == 2) {
      Term arg1 = constraint.queryArgument(1);
      Term arg2 = constraint.queryArgument(2);
      ArrayList<Term> ret = new ArrayList<Term>();
      ret.add(TermFactory.createApp(TheoryFactory.greaterSymbol, arg1, arg2));
      ret.add(TermFactory.createApp(TheoryFactory.smallerSymbol, arg1, arg2));
      return Optional.of(ret);
    }
    if (constraint.queryRoot().equals(TheoryFactory.orSymbol)) {
      ArrayList<Term> ret = new ArrayList<Term>();
      addJunctionParts(constraint, TheoryFactory.orSymbol, ret);
      return Optional.of(ret);
    }
    return Optional.empty();
  }

  /** Returns a /\ b. */
  private Term makeConj(Term a, Term b) {
    return TermFactory.createApp(TheoryFactory.andSymbol, a, b);
  }

  /** Turns a list [C1,...,Cn] into [C1 /\ addition,...,Cn /\ addition]. */
  private void combine(ArrayList<Term> constraintlist, Term addition) {
    for (int i = 0; i < constraintlist.size(); i++) {
      constraintlist.set(i, makeConj(constraintlist.get(i), addition));
    }
  }

  /**
   * Given lists [C1,...,Cn] and [D1,...,Dm], this updates constraintlist to contain all
   * combinations Ci /\ Dj.
   */
  private void multiply(ArrayList<Term> constraintlist, ArrayList<Term> otherlist) {
    int n = constraintlist.size();
    for (int j = 1; j < otherlist.size(); j++) {
      for (int i = 0; i < n; i++) {
        constraintlist.add(makeConj(constraintlist.get(i), otherlist.get(j)));
      }
    }
    for (int i = 0; i < n; i++) {
      constraintlist.set(i, makeConj(constraintlist.get(i), otherlist.get(0)));
    }
  }

  private Optional<ArrayList<DP>> split(DP dp) {
    Term constraint = dp.constraint();
    ArrayList<Term> parts = getConjunctionComponents(constraint);
    ArrayList<Term> results;
    int numSplit = 0;

    // let results = <the splitted versions of the first constraint>
    Optional<ArrayList<Term>> first = split(parts.get(0));
    if (first.isEmpty()) {
      results = new ArrayList<Term>();
      results.add(parts.get(0));
    }
    else {
      results = first.get();
      numSplit = 1;
    }

    for (int i = 1; i < parts.size(); i++) {
      // let results = <the splitted version of the first i constraints>
      Optional<ArrayList<Term>> next = split(parts.get(i));
      if (next.isEmpty()) combine(results, parts.get(i));
      else {
        numSplit++;
        if (numSplit > 2) return Optional.empty();  // this is getting to be too much!
        multiply(results, next.get());
      }
    }
    if (numSplit == 0) return Optional.empty();
    ArrayList<DP> ret = new ArrayList<DP>();
    for (int i = 0; i < results.size(); i++) {
      ret.add(new DP(dp.lhs(), dp.rhs(), results.get(i), dp.vars(), dp.isPrivate()));
    }
    return Optional.of(ret);
  }

  @Override
  public Optional<List<Problem>> processDPP(Problem dpp) {
    List<DP> dps = dpp.getDPList();
    ArrayList<DP> ret = new ArrayList<DP>();
    boolean anychanges = false;
    for (int i = 0; i < dps.size(); i++) {
      Optional<ArrayList<DP>> splitDP = split(dps.get(i));
      if (splitDP.isEmpty()) ret.add(dps.get(i));
      else {
        anychanges = true;
        for (DP dp : splitDP.get()) ret.add(dp);
      }
    }
    if (anychanges) return Optional.of(List.of(new Problem(ret, dpp.getTRS())));
    else return Optional.empty();
  }
}
