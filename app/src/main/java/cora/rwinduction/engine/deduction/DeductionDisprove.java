/**************************************************************************************************
 Copyright 2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rwinduction.engine.deduction;

import java.util.Optional;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.terms.replaceable.Renaming;
import charlie.terms.FunctionSymbol;
import charlie.terms.Term;
import charlie.terms.Value;
import charlie.terms.TheoryFactory;
import charlie.terms.Substitution;
import charlie.theorytranslation.TermAnalyser;
import charlie.printer.Printer;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

public final class DeductionDisprove extends DeductionStep {
  private Term _constraint;
    // either null, or something that should be satisfiable for the disprove to succeed
  private Substitution _substitution;
    // if not null, this is a substitution that makes the constraint of the equation true, but the
    // two sides unequal
  private Pair<FunctionSymbol,FunctionSymbol> _differentRoots;
    // either null, or a pair of function symbols that the lhs and rhs of the equation can be
    // instantiated to have as their respective root symbols

  private DeductionDisprove(ProofState state, ProofContext context, Term constraint) {
    super(state, context);
    _constraint = constraint;
    _substitution = null;
    _differentRoots = null;
  }

  private DeductionDisprove(ProofState state, ProofContext context,
                            Pair<FunctionSymbol,FunctionSymbol> roots) {
    super(state, context);
    _differentRoots = roots;
    _constraint = null;
    _substitution = null;
  }

  public static DeductionDisprove createStep(PartialProof proof, Optional<OutputModule> m) {
    Equation equation = getTopEquation(proof.getProofState(), m);
    if (equation == null) return null;
    Term left = equation.getLhs();
    Term right = equation.getRhs();

    // balk if the equation we're looking at is not complete
    int index = proof.getProofState().getTopEquation().getIndex();
    if (proof.getProofState().getIncompleteEquations().contains(index)) {
      m.ifPresent(o -> o.println("DISPROVE can only be applied on complete equation contexts."));
      return null;
    }
    
    // option 1: the sides have different root symbols, with fewer arguments than their rule arity
    DeductionDisprove ret = createDifferentRootsStep(proof, left, right);
    if (ret != null) return ret;

    // option 2: both sides are (base-type) theory terms -- we should check their satisfiability
    ret = createDifferentTheoryStep(proof, left, right, equation.getConstraint());
    if (ret != null) return ret;

    m.ifPresent(o -> o.println("The left- and right-hand side cannot (obviously) be instantiated " +
      "to distinct semi-constructor terms (by the same substitution), yet they are also not " +
      "both theory terms."));

    return null;
  }

  /**
   * If the top equation in the current proof state has a left-hand side and right-hand side that
   * can obviously be instantiated to semi-constructor terms with different function symbols at the
   * roots, then this returns the pair of symbols that we can have at the root.
   * Otherwise, it returns null.
   */
  public static Pair<FunctionSymbol,FunctionSymbol> checkDifferentSemiconstructors(Term left,
                                                            Term right, ProofContext context) {
    if (left.queryHead().equals(right.queryHead())) return null;
    FunctionSymbol f = null, g = null;
    if (left.isFunctionalTerm()) {
      f = left.queryRoot();
      if (left.numberArguments() >= context.queryRuleArity(f)) return null;
    }
    if (right.isFunctionalTerm()) {
      g = right.queryRoot();
      if (right.numberArguments() >= context.queryRuleArity(g)) return null;
    }
    if (f == null) {
      f = findSemiConstructor(context, left.queryHead().queryType(), left.numberArguments(), g);
    }
    if (g == null) {
      g = findSemiConstructor(context, right.queryHead().queryType(), right.numberArguments(), f);
    }
    if (f != null && g != null) return new Pair<FunctionSymbol,FunctionSymbol>(f, g);
    return null;
  }

  /**
   * This returns a function symbol f so that arguments a1...an exist such that:
   * - f(a1,...,an) has type otype
   * - f has rule arity > n + numargs
   * - f is not h (note that h is allowed to be null, in which case nothing is excluded)
   * If such a function symbol f does not exist, then null is returned instead.
   */
  private static FunctionSymbol findSemiConstructor(ProofContext context,
                                                    Type otype, int numargs, FunctionSymbol h) {
    int oar = otype.queryArity();
    for (FunctionSymbol f : context.getTRS().queryAlphabet().getSymbols()) {
      // check: f != h
      if (f == h) continue;
      // compute n knowing that IF f(a1,...,an) :: otype, then arity(f) = n + arity(otype),
      // so n = arity(f) - arity(otype) ≥ 0
      Type t = f.queryType();
      int k = t.queryArity();
      if (k < oar) continue;
      int n = k - oar;
      // check: f has rule arity > n + numargs
      if (context.queryRuleArity(f) <= n + numargs) continue;
      // check: the type of f(a1,...,an) is indeed otype
      for (int i = 0; i < n; i++) t = t.subtype(2);
      if (t.equals(otype)) return f;
    }
    return null;
  }

  /**
   * If the left-hand side and right-hand side can be instantiated to have different root symbols,
   * then this returns the corresponding DeductionDisprove; if this is not obviously the case, then
   * null is returned instead (but no error message is given).
   */
  private static DeductionDisprove createDifferentRootsStep(PartialProof proof,
                                                            Term left, Term right) {
    ProofContext context = proof.getContext();
    Pair<FunctionSymbol,FunctionSymbol> pair = checkDifferentSemiconstructors(left, right, context);
    if (pair == null) return null;
    return new DeductionDisprove(proof.getProofState(), context, pair);
  }

  private static DeductionDisprove createDifferentTheoryStep(PartialProof proof, Term left,
                                                             Term right, Term constr) {
    if (!left.isTheoryTerm() || !right.isTheoryTerm()) return null;
    if (!left.isFirstOrder() || !right.isFirstOrder()) return null;
    Term constraint = TheoryFactory.createConjunction(constr, TheoryFactory.notSymbol.apply(
      TheoryFactory.createEquality(left, right)));
    return new DeductionDisprove(proof.getProofState(), proof.getContext(), constraint);
  }

  @Override
  public boolean verify(Optional<OutputModule> module) {
    if (_constraint == null) return true; // nothing to verify

    switch (TermAnalyser.satisfy(_constraint, Settings.smtSolver)) {
      case TermAnalyser.Result.YES(Substitution subst):
        _substitution = subst;
        return true;
      default: return false;
    }
  }

  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    return ProofState.getContradictionState();
  }

  @Override
  public String commandDescription() {
    return "disprove";
  }

  @Override
  public void explain(OutputModule module) {
    if (_differentRoots != null) {
      FunctionSymbol f = _differentRoots.fst();
      String extra1 = f.queryType().equals(_equ.getEquation().getLhs().queryType()) ? "" : "(...)";
      FunctionSymbol g = _differentRoots.snd();
      String extra2 = g.queryType().equals(_equ.getEquation().getRhs().queryType()) ? "" : "(...)";
      module.println("We apply DISPROVE to %a, which succeeds because the sides can be " +
        "instantiated to distinct semi-constructor terms; respectively %a%a and %a%a.",
          _equ.getName(), f.queryName(), extra1, g.queryName(), extra2);
    }
    else if (_substitution == null) {
      module.println("We apply DISPROVE to %a, which succeeds because the constraint %a is " +
        "satisfiable.", _equ.getName(), Printer.makePrintable(_constraint, _equ.getRenaming()));
    }
    else {
      Value l = TermAnalyser.evaluate(_equ.getEquation().getLhs().substitute(_substitution));
      Value r = TermAnalyser.evaluate(_equ.getEquation().getRhs().substitute(_substitution));
      Renaming renaming = _equ.getRenaming();
      module.println("We apply DISPROVE to %a, which succeeds because under the substitution %a, " +
        "the constraint %a evaluates to true, while the sides of the equation can be calculated " +
        "to %a and %a respectively.", _equ.getName(),
        Printer.makePrintable(_substitution, _equ.getRenaming(), _equ.getRenaming()),
        _equ.getEquation().getConstraint(), l, r);
    }
  }
}

