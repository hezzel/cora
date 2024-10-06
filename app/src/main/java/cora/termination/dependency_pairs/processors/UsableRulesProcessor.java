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

import charlie.util.Pair;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.trs.TrsProperties.*;
import charlie.trs.TrsFactory;
import cora.io.OutputModule;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;

import java.util.List;
import java.util.LinkedList;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

public class UsableRulesProcessor implements Processor {
  /** This method has only been defined for innermost LCSTRSs */
  public boolean isApplicable(Problem dpp) {
    return dpp.isInnermost() &&
           dpp.getOriginalTRS().verifyProperties(Level.APPLICATIVE, Constrained.YES,
                                                 Products.DISALLOWED, Lhs.PATTERN, Root.THEORY);
  }

  /**
   * Creates a map that returns, for every function symbol f, a list of all rules whose left-hand
   * side has f as the root symbol.
   */
  private TreeMap<FunctionSymbol,LinkedList<Rule>> indexRulesByRoot(List<Rule> source) {
    TreeMap<FunctionSymbol,LinkedList<Rule>> ret = new TreeMap<FunctionSymbol,LinkedList<Rule>>();
    for (Rule rho : source) {
      FunctionSymbol f = rho.queryRoot();
      LinkedList<Rule> lst = ret.get(f);
      if (lst == null) { lst = new LinkedList<Rule>(); ret.put(f, lst); }
      lst.add(rho);
    }
    return ret;
  }

  private class BoolWrapper { boolean b; }

  /**
   * Returns all the usable symbols of the given DP problem, or null if the set of usable symbols
   * contains ⊥ (that is, there is a "usable subterm" of the form F(s1,...,sn) with n > 0 and F a
   * variable).  The "index" parameter maps each function symbol to the corresponding list of rules.
   *
   * Default rather than private only for the sake of unit testing.
   */
  private TreeMap<FunctionSymbol,TreeSet<Integer>> computeUsableSymbols(Problem dpp,
                                     TreeMap<FunctionSymbol,LinkedList<Rule>> index) {
    TreeMap<FunctionSymbol,TreeSet<Integer>> ret = new TreeMap<FunctionSymbol,TreeSet<Integer>>();
    LinkedList<Term> todo = new LinkedList<Term>();
    BoolWrapper containsBad = new BoolWrapper(); containsBad.b = false;
    for (DP dp : dpp.getDPList()) todo.add(dp.rhs());
    while (!todo.isEmpty() && !containsBad.b) {
      Term t = todo.pop();
      t.visitSubterms( (s,p) -> {
        if (s.isVarTerm() && s.numberArguments() > 0) containsBad.b = true;
        if (s.isFunctionalTerm()) {
          FunctionSymbol f = s.queryRoot();
          updateUsableSymbols(f, s.numberArguments(), index.get(f), ret, todo);
        }
      });
      if (containsBad.b) return null;
    }
    return ret;
  }

  /**
   * Helper function for computeUsableSymbols.  The set rules lists all the rules we need to
   * consider whose left-hand side has a root symbol f, or is null if f is a constructor.
   * This function updates the sets symbols and todo to include (f,n) in symbols, and add new
   * right-hand sides of rules to be considered for their usable symbols.
   */
  private void updateUsableSymbols(FunctionSymbol f, int n, List<Rule> rules,
                                   TreeMap<FunctionSymbol,TreeSet<Integer>> symbols,
                                   LinkedList<Term> todo) {
    // if f is a constructor, there's nothing for us to do!
    if (rules == null) return;
    
    // if (f,n) is already in symbols, return; if not, add it
    TreeSet<Integer> set = symbols.get(f);
    if (set == null) {
      set = new TreeSet<Integer>();
      symbols.put(f, set);
    }
    else if (set.contains(n)) return;
    set.add(n);

    // add the appropriate right-hand sides to the todo list
    for (Rule rule : rules) {
      int k = rule.queryLeftSide().numberArguments();
      if (k <= n) {
        Term t = rule.queryRightSide();
        for (; k < n; k++) {
          Variable x = TermFactory.createVar(t.queryType().subtype(1));
          t = t.apply(x);
        }
        todo.add(t);
      }
    }
  }

  /** Solely for unit testing: returns a string representation of the usable symbols. */
  String printUsableSymbols(Problem dpp) {
    TreeMap<FunctionSymbol,LinkedList<Rule>> index = indexRulesByRoot(dpp.getRuleList());
    TreeMap<FunctionSymbol,TreeSet<Integer>> ret = computeUsableSymbols(dpp, index);
    if (ret == null) return "NA";
    StringBuilder answer = new StringBuilder();
    for (Map.Entry<FunctionSymbol,TreeSet<Integer>> entry : ret.entrySet()) {
      for (int i : entry.getValue()) {
        answer.append("(" + entry.getKey() + "," + i + ") ");
      }
    }
    return answer.toString();
  }

  /**
   * For a given rule f(l1,...,lk) → r, this returns either null -- if usableIndexes does not
   * contain any element n ≥ k -- or if such an n exists, then it returns f(l1,...,lk,x{k+1},...,
   * xn) for the smallest such n.
   */
  private Rule getUsableForm(Rule rho, TreeSet<Integer> usableIndexes) {
    Term left = rho.queryLeftSide();
    FunctionSymbol f = left.queryRoot();
    int k = left.numberArguments();
    for (int n : usableIndexes) { // it's a TreeSet, so we go through this set from small to large
      if (n < k) continue;
      if (n == k) return rho;
      Term right = rho.queryRightSide();
      for (int i = k+1; i <= n; i++) {
        Variable x = TermFactory.createVar("arg" + (i+1), left.queryType().subtype(1));
        left = left.apply(x);
        right = right.apply(x);
      }
      return TrsFactory.createRule(left, right, rho.queryConstraint());
    }
    return null;  // there were no elements in this set ≥ k
  }

  /**
   * Given the usable symbols (and given that the method applies), and the output of
   * indexRulesByRoot, this returns the usable rules.
   * However, if the usable rules are exactly the same as the original rules, this returns null
   * instead.
   */
  private List<Rule> computeUsableRules(TreeMap<FunctionSymbol,TreeSet<Integer>> usableSymbols,
                                        TreeMap<FunctionSymbol,LinkedList<Rule>> index,
                                        int originalRuleCount) {
    int rulesFromOriginal = 0;
    LinkedList<Rule> ret = new LinkedList<Rule>();
    for (Map.Entry<FunctionSymbol,TreeSet<Integer>> entry : usableSymbols.entrySet()) {
      FunctionSymbol f = entry.getKey();
      LinkedList<Rule> relevant = index.get(f);
      if (relevant != null) {
        for (Rule rho : relevant) {
          Rule rule = getUsableForm(rho, entry.getValue());
          if (rule != null) ret.add(rule);
          if (rule == rho) rulesFromOriginal++;
        }
      }
    }
    if (rulesFromOriginal == originalRuleCount) return null;  // we didn't change anything!
    return ret; // we did change something!
  }

  /** Runs the processor, trying to remove one or more rules */
  public ProcessorProofObject processDPP(Problem dpp) {
    // compute the usable rules
    List<Rule> orgrules = dpp.getRuleList();
    TreeMap<FunctionSymbol,LinkedList<Rule>> index = indexRulesByRoot(orgrules);
    TreeMap<FunctionSymbol,TreeSet<Integer>> usableSymbols = computeUsableSymbols(dpp, index);
    if (usableSymbols == null) {
      return new URProofObject(dpp, "The Usable Rules method is not applicable.");
    }
    List<Rule> ret = computeUsableRules(usableSymbols, index, orgrules.size());

    // handle the case where everything is usable
    String message = null;
    if (ret == null) {
      if (!dpp.hasExtraRules()) return new URProofObject(dpp, "All rules are usable.");
      ret = orgrules;
      message = "All known rules are usable, but the Usable Rules method is applicable so the " +
        "extra rules are not usable, and may be dropped.";
    }

    // compute the new DP, and store an appropriate message for the output module
    Problem result = new Problem(dpp.getDPList(), ret, dpp.queryPrivateIndexes(),
                                 dpp.getOriginalTRS(), dpp.isInnermost(), false,
                                 dpp.queryTerminationStatus());
    if (message == null) message = "We obtain " + ret.size() + " usable rules (out of " +
      orgrules.size() + " rules in the input problem).";
    return new URProofObject(dpp, result, message);
  }
}

class URProofObject extends ProcessorProofObject {
  String _explanation;
  /** Constructor for a failed proof */
  URProofObject(Problem dpp, String expl) { super(dpp); _explanation = expl; }
  /** Constructor for a successful proof (at least one rule was removed, or the extra rules were) */
  URProofObject(Problem in, Problem out, String expl) { super(in, out); _explanation = expl; }
  /** Returns the name of the processor for printing */
  public String queryProcessorName() { return "Usable Rules"; }
  /** Justify the answer for output to the user */
  public void justify(OutputModule module) { module.println("%a", _explanation); }
}

