/**************************************************************************************************
 Copyright 2025 Cynthia Kop & Liye Guo

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.confluence;

import java.util.Collection;
import java.util.LinkedList;

import charlie.terms.position.Position;
import charlie.terms.position.FinalPos;
import charlie.terms.*;
import charlie.substitution.MutableSubstitution;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.trs.TrsFactory;
import charlie.trs.TrsProperties;
import charlie.theorytranslation.TermAnalyser;
import charlie.substitution.Unifier;
import cora.config.Settings;

/** Finds the critical peaks of an LCSTRS. */
public class CriticalPeaksFinder {
  /** Collects the critical peaks. */
  private final LinkedList<CriticalPeak> _cps = new LinkedList<>();
  /** Keeps track of whether we should include non-trivial critical peaks. */
  private boolean _nontrivial;

  /** The constructor is private and only accessible inside the class. */
  private CriticalPeaksFinder(boolean includeNontrivial) {
    _nontrivial = includeNontrivial;
  }

  /**
   * Generates a critical peak (if possible) and stores it in _cps.
   * @param subterm is at position in source's lhs.
   * @param target is a rule with disjoint variables from source
   * @param nontrivial indicates whether trivial critical peaks are excluded.
   *
   * For this function to be called, we require that the left-hand side of target has a form
   * f l1 ... lk (this is part of the TRS restriction for applying this technique), and that
   * subterm has a form f t1 ... tn with n ≥ k.
   */
  private void generateCpForDefinedSymbol(Term subterm, Position position,
                                          Rule source, Rule target) {
    // Find subst so that (f l1 ... lk) subst = (f t1 ... tk) subst
    var taLhs = target.queryLeftSide();
    var subst = Unifier.mgu(taLhs, subterm.queryImmediateHeadSubterm(taLhs.numberArguments()));
    if (subst == null) return;

    // We require that all constraint-variables of both source and target are instantiated by
    // values or variables.  (If some variable is not substituted, then it is mapped to itself,
    // so a variable.)
    for (var x : target.queryLVars()) {
      var t = subst.getReplacement(x);
      if (!t.isValue() && !t.isVariable()) return;
    }
    for (var x : source.queryLVars()) {
      var t = subst.getReplacement(x);
      if (!t.isValue() && !t.isVariable()) return;
    }

    // the combined constraint must be satisfiable for this to give a critical pair
    var con = TheoryFactory.createConjunction(
      subst.substitute(target.queryConstraint()),
      subst.substitute(source.queryConstraint()));
    var result = TermAnalyser.satisfy(con, Settings.smtSolver);
    if (result instanceof TermAnalyser.Result.NO) return;

    // all requirements are satisfied; compute the critical pair
    var lhs = source.queryLeftSide().replaceSubterm(
      position.append(new FinalPos(subterm.numberArguments() - taLhs.numberArguments())),
      subst.substitute(target.queryRightSide()));
    var rhs = subst.substitute(source.queryRightSide());
    if (_nontrivial && lhs.equals(rhs)) return;

    var top = subst.substitute(source.queryLeftSide());
    _cps.add(new CriticalPeak(top, lhs, rhs, con));
  }

  /**
   * Given that [subterm] is the subterm at position [position] of the left-hand side of rule, and
   * that rule has been renamed to be disjoint from all other rules in [trs], this function stores
   * all critical peaks caused by an overlap between [subterm] and the root of another (or the
   * same) rule.
   *
   * To avoid duplicates, this function does not consider root overlaps other than overlaps with a
   * calculation rule.
   */
  private void generateCriticalPairsForSubterm(Term subterm, Position pos, TRS trs, Rule rule) {
    if (!subterm.isFunctionalTerm()) return;
    FunctionSymbol root = subterm.queryRoot();
    int nargs = subterm.numberArguments();

    /* Here only nonempty positions are considered for defined symbols;
     * empty ones are handled separately. */
    if (!pos.isEmpty()) {
      trs.queryRulesForSymbol(root, false).forEach(target -> {
        if (nargs >= target.queryLeftSide().numberArguments()) {
          generateCpForDefinedSymbol(subterm, pos, rule, target);
        }
      });
    }

    /* For calculation symbols, a critical pair is generated more "lightly". */
    if (root.isTheorySymbol() && nargs > 0 && subterm.queryType().isBaseType() &&
        subterm.queryArguments().stream().allMatch(t -> t.isValue() || t.isVariable())) {
      /* The name _z is arbitrary and included for testing. */
      var z = TermFactory.createVar("_z", subterm.queryType());
      _cps.add(new CriticalPeak(
        rule.queryLeftSide(),
        rule.queryLeftSide().replaceSubterm(pos, z),
        rule.queryRightSide(),
        TheoryFactory.createConjunction(
          TheoryFactory.createEquality(z, subterm),
          rule.queryConstraint())));
    }
  }

  /**
   * This considers a rule overlap between a rule with (a renamed version of) itself, i.e., an
   * overlap at the empty position.  Note that for this to give a critical pair, there must be a
   * variable on the rhs that does not occur on the lhs.
   */
  private void generateCriticalPairsForSelfRootOverlap(Rule renamed, Rule original) {
    if (original.queryRightReplaceablePolicy() == TrsProperties.FreshRight.NONE) return;
    generateCpForDefinedSymbol(renamed.queryLeftSide(), new FinalPos(0), renamed, original);
  }

  /**
   * Given that rule1 and rule2 are distinct rules, and also with distinct variables, this
   * computes the critical pair between them generated by a root overlap, if any.
   */
  private void generateCriticalPairsForRootOverlap(Rule rule1, Rule rule2) {
    /* Note that it is vital to check which rule's lhs has more arguments than the other's
     * before calling generateCpForDefinedSymbol, due to possible partial application. */
    if (rule1.queryLeftSide().numberArguments() >= rule2.queryLeftSide().numberArguments()) {
      generateCpForDefinedSymbol(rule1.queryLeftSide(), new FinalPos(0), rule1, rule2);
    }
    else {
      generateCpForDefinedSymbol(rule2.queryLeftSide(), new FinalPos(0), rule2, rule1);
    }
  }

  /**
   * Generates a renamed version of the given rule.  (Note that rules are limited to
   * variables, not meta-variables.)
   */
  private static Rule renameRule(Rule rule) {
    MutableSubstitution subst = new MutableSubstitution();
    for (var x : rule.queryAllReplaceables()) {
      subst.extend(x, TermFactory.createVar(x.queryName(), x.queryType()));
    }
    return TrsFactory.createRule(
      subst.substitute(rule.queryLeftSide()),
      subst.substitute(rule.queryRightSide()),
      subst.substitute(rule.queryConstraint()));
  }

  /**
   * The method for critical peaks, publicly accessible.
   * @return the critical peaks of trs, including trivial ones unless nontrivial is true.
   */
  public static Collection<CriticalPeak> criticalPeaks(TRS trs, boolean nontrivial) {
    if (!trs.verifyProperties(TrsProperties.Level.APPLICATIVE, TrsProperties.Constrained.YES,
                              TrsProperties.TypeLevel.SIMPLE, TrsProperties.Lhs.PATTERN,
                              TrsProperties.Root.THEORY, TrsProperties.FreshRight.CVARS)) {
      throw new IllegalArgumentException("Invalid input TRS.");
    }
    
    var finder = new CriticalPeaksFinder(nontrivial);
    var trsRul = trs.queryRules();
    var nRules = trsRul.size();

    for (int i = 0; i < nRules; i++) {
      Rule renamed = renameRule(trsRul.get(i));

      // All non-root overlaps, or root overlaps with a calculation rule.
      renamed.queryLeftSide().visitSubterms((s, p) ->
        finder.generateCriticalPairsForSubterm(s, p, trs, renamed));
      
      // Overlaps of a rule with itself at the root.
      finder.generateCriticalPairsForSelfRootOverlap(renamed, trsRul.get(i));

      // Overlaps of renamed with a different rule at the root.
      // All _unordered_ pairs of distinct rules are considered to avoid duplicates modulo symmetry.
      for (int j = i + 1; j < nRules; j++) {
        finder.generateCriticalPairsForRootOverlap(renamed, trsRul.get(j));
      }
    }
    return finder._cps;
  }
}
