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

import charlie.terms.Term;
import charlie.terms.TermFactory;
import charlie.terms.TheoryFactory;
import charlie.terms.position.Position;
import charlie.terms.position.FinalPos;
import charlie.theorytranslation.TermAnalyser;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.trs.TrsFactory;
import charlie.trs.TrsProperties;
import charlie.unification.MguFinder;
import cora.config.Settings;

import java.util.Collection;
import java.util.LinkedList;

/** Finds the critical peaks of an LCSTRS. */
public class CriticalPeaksFinder {
  /** Collects the critical peaks. */
  private final LinkedList<CriticalPeak> _cps = new LinkedList<>();

  /** The constructor is private and only accessible inside the class. */
  private CriticalPeaksFinder() {}

  /** Generates a renamed version of the given rule. */
  private static Rule renameRule(Rule rule) {
    var subst = TermFactory.createEmptySubstitution();
    for (var x : rule.queryAllReplaceables()) {
      subst.extend(x, TermFactory.createVar(x.queryName(), x.queryType()));
    }
    return TrsFactory.createRule(
      rule.queryLeftSide().substitute(subst),
      rule.queryRightSide().substitute(subst),
      rule.queryConstraint().substitute(subst));
  }

  /**
   * Generates a critical peak (if possible) and stores it in _cps.
   * @param subterm is at position in source's lhs.
   * @param target's lhs must not have more arguments than subterm does.
   * @param nontrivial indicates whether trivial critical peaks are excluded.
   */
  private void generateCpForDefinedSymbol(Term subterm, Position position,
                                          Rule source, Rule target, boolean nontrivial) {
    var taLhs = target.queryLeftSide();
    var subst = MguFinder.mgu(taLhs, subterm.queryImmediateHeadSubterm(taLhs.numberArguments()));
    if (subst == null) return;

    for (var x : target.queryLVars()) {
      var t = subst.getReplacement(x);
      if (!t.isValue() && !t.isVariable()) return;
    }
    for (var x : source.queryLVars()) {
      var t = subst.getReplacement(x);
      if (!t.isValue() && !t.isVariable()) return;
    }

    var con = TheoryFactory.createConjunction(
      target.queryConstraint().substitute(subst),
      source.queryConstraint().substitute(subst));
    var result = TermAnalyser.satisfy(con, Settings.smtSolver);
    if (result instanceof TermAnalyser.Result.NO) return;

    var lhs = source.queryLeftSide().replaceSubterm(
      position.append(new FinalPos(subterm.numberArguments() - taLhs.numberArguments())),
      target.queryRightSide()).substitute(subst);
    var rhs = source.queryRightSide().substitute(subst);
    if (nontrivial && lhs.equals(rhs)) return;

    var top = source.queryLeftSide().substitute(subst);
    _cps.add(new CriticalPeak(top, lhs, rhs, con));
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
    var finder = new CriticalPeaksFinder();
    var trsRul = trs.queryRules();
    var nRules = trsRul.size();
    for (int i = 0; i < nRules; i++) {
      var renamed = renameRule(trsRul.get(i));
      renamed.queryLeftSide().visitSubterms((s, p) -> {
        if (s.isFunctionalTerm()) {
          /* Here only nonempty positions are considered for defined symbols;
           * empty ones are handled separately.
           */
          if (!p.isEmpty()) {
            trs.queryRulesForSymbol(s.queryRoot(), false).forEach(target -> {
              if (s.numberArguments() >= target.queryLeftSide().numberArguments()) {
                finder.generateCpForDefinedSymbol(s, p, renamed, target, nontrivial);
              }
            });
          }
          /* For calculation symbols, a critical pair is generated more "lightly". */
          if (s.queryRoot().isTheorySymbol() &&
            s.numberArguments() > 0 &&
            s.queryType().isBaseType() &&
            s.queryArguments().stream().allMatch(
              t -> t.isValue() || t.isVariable())) {
            /* The name _z is arbitrary and included for testing. */
            var z = TermFactory.createVar("_z", s.queryType());
            finder._cps.add(new CriticalPeak(
              renamed.queryLeftSide(),
              renamed.queryLeftSide().replaceSubterm(p, z),
              renamed.queryRightSide(),
              TheoryFactory.createConjunction(
                TheoryFactory.createEquality(z, s),
                renamed.queryConstraint())));
          }
        }
      });
      /* The first case for defined symbols at the root, i.e., the empty position:
       * (a renaming of) the same rule at the root,
       * in which case there must be a variable on the rhs but not on the lhs.
       */
      if (trsRul.get(i).queryRightReplaceablePolicy() != TrsProperties.FreshRight.NONE) {
        finder.generateCpForDefinedSymbol(
          renamed.queryLeftSide(), new FinalPos(0),
          renamed, trsRul.get(i), nontrivial);
      }
      /* The second case: a different rule.
       * All _unordered_ pairs of distinct rules are considered to avoid duplicates modulo symmetry.
       * Note that it is vital to check which rule's lhs has more arguments than the other's
       * before calling generateCpForDefinedSymbol, due to possible partial application.
       */
      for (int j = i + 1; j < nRules; j++) {
        var target = trsRul.get(j);
        if (renamed.queryLeftSide().numberArguments()
          >= target.queryLeftSide().numberArguments()) {
          finder.generateCpForDefinedSymbol(
            renamed.queryLeftSide(), new FinalPos(0),
            renamed, target, nontrivial);
        }
        else {
          finder.generateCpForDefinedSymbol(
            target.queryLeftSide(), new FinalPos(0),
            target, renamed, nontrivial);
        }
      }
    }
    return finder._cps;
  }
}
