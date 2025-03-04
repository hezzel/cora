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
import java.util.TreeSet;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import charlie.theorytranslation.TermSmtTranslator;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/** The deduction command for simplifying an equation with an induction hypothesis */
public final class DeductionHypothesis extends DeductionStep {
  private ConstrainedReductionHelper _helper;
  private String _hypothesisName;
  private boolean _inversed;
  private Optional<OrdReq> _requirement;
  private Equation _result;
  private boolean _doneAfter;

  /** Private constructor, called (only) by createStep */
  private DeductionHypothesis(ProofState state, ProofContext context, String hypoName,
                            boolean inverse, ConstrainedReductionHelper h, Equation result,
                            OrdReq req, boolean deletable) {
    super(state, context);
    _helper = h;
    _hypothesisName = hypoName;
    _inversed = inverse;
    _result = result;
    if (req == null) _requirement = Optional.empty();
    else _requirement = Optional.of(req);
    _doneAfter = deletable;
  }

  /**
   * This either returns the hypothesis with the given name in the current proof state, or prints
   * an error message to m and returns false.
   */
  private static Hypothesis getHypothesisByName(PartialProof proof, String name,
                                                Optional<OutputModule> m) {
    for (Hypothesis h : proof.getProofState().getHypotheses()) {
      if (h.getName().equals(name)) return h;
    }
    m.ifPresent(o -> o.println("No such induction hypothesis: %a", name));
    return null;
  }

  /**
   * This returns the ordering requirement that should be imposed.  This ordering requirement is
   * built using the constraint from result (which should be the same as the constraint from
   * original) and the Renaming from result; hence, for the ordering requirement to not be
   * ill-formed, this method requires that the reduction does not introduce fresh variables!
   */
  private static OrdReq getOrderingRequirement(EquationContext original, Equation result,
                                               boolean orderFromOtherSide, EquationPosition pos) {
    // if either of the "greater terms" of result is •, then it is automatically greater than any
    // term, so we do not need to require anything
    if (original.getLeftGreaterTerm().isEmpty()) return null;
    if (original.getRightGreaterTerm().isEmpty()) return null;
    // otherwise, we must have either leftterm ≻ [result of reduction] or rightterm ≻ [result of
    // reduction]
    Term rightOfReq = result.querySubterm(pos);
    // we use the following heuristic for reducing (s', C[u] = t, t') to (s', C[v] = t, t'): we
    // choose s' ≻ v, unless c[v] equals t, in which case we choose t' ≻ v; if instead the
    // reduction is on the right, we take the symmetric choice
    boolean redOnLeft = pos.querySide() == EquationPosition.Side.Left;
    Term leftOfReq;
    if (orderFromOtherSide) {
      if (redOnLeft) leftOfReq = original.getRightGreaterTerm().get();
      else leftOfReq = original.getLeftGreaterTerm().get();
    }
    else {
      if (redOnLeft) leftOfReq = original.getLeftGreaterTerm().get();
      else leftOfReq = original.getRightGreaterTerm().get();
    }
    // construct the ordering requirement!
    return new OrdReq(leftOfReq, rightOfReq, result.getConstraint(), original.getRenaming());
  }

  /**
   * Creates a simplification-with-hypothesis step for the given information, checking that there
   * is indeed a match but NOT that the constraint is satisfied or that no new variables are
   * created.
   * The substitution will not be altered, and does not become the property of the step; it is
   * safe to change afterwards.
   * For now, the step decides for itself which ordering requirement is imposed; the user cannot
   * indicate this.  This is likely to be changed in the future, though.
   */
  public static Optional<DeductionHypothesis> createStep(PartialProof proof, Optional<OutputModule> m,
                                                         String hypoName, boolean inverse,
                                                         EquationPosition pos, Substitution subst) {
    Hypothesis hypo = getHypothesisByName(proof, hypoName, m);
    if (hypo == null) return Optional.empty();
    Equation hequ = hypo.getEquation();
    Term left = inverse ? hequ.getRhs() : hequ.getLhs();
    Term right = inverse ? hequ.getLhs() : hequ.getRhs();

    ConstrainedReductionHelper helper =
      new ConstrainedReductionHelper(left, right, hequ.getConstraint(), hypo.getRenaming(), pos,
                                     subst, "induction hypothesis");
    if (!helper.extendSubstitution(getTopEquation(proof.getProofState(), m), m)) {
      return Optional.empty();
    }
    if (!helper.checkEverythingSubstituted(m)) return Optional.empty();

    EquationContext current = proof.getProofState().getTopEquation();
    Equation result = helper.reduce(current.getEquation(), m);
    boolean deletable = result.getLhs().equals(result.getRhs());
    OrdReq req = getOrderingRequirement(current, result, deletable, pos);

    return Optional.of(new DeductionHypothesis(proof.getProofState(), proof.getContext(),
                                               hypoName + (inverse ? "^{-1}" : ""), inverse,
                                               helper, result, req, deletable));
  }

  /**
   * This function checks if we can indeed apply the induction hypothesis in the direction l → r | φ
   * with the substitution γ to the equation C[lγ]_p ≈ t | ψ, with data as given by step.  Note
   * that, for a step to be created, it is already given that l γ is indeed the subterm at the given
   * position of the equation.  Hence, the remaining checks are:
   * - check that all (meta-)vars in the rule are in dom(δ)
   * - check that ψ ⇒ φδ is valid
   */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    if (_helper.constraintIsTrue()) return true;
    Term constraint = _equ.getEquation().getConstraint();
    return _helper.checkConstraintGoodForReduction(_equ.getEquation().getConstraint(),
                                                   _equ.getRenaming(), module,
                                                   Settings.smtSolver);
  }

  @Override
  protected ProofState tryApply(Optional<OutputModule> module) {
    EquationContext newequ = _equ.replace(_result, _state.getLastUsedIndex() + 1);

    ProofState tmp =
      _requirement.isEmpty() ? _state : _state.addOrderingRequirement(_requirement.get());
    if (_doneAfter) return tmp.deleteTopEquation();
    else return tmp.replaceTopEquation(newequ);
  }

  @Override
  public String commandDescription() {
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add("hypothesis ", _hypothesisName, " ", _helper.queryPosition(), " with ",
      _helper.substitutionPrintable(_equ.getRenaming()));
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    module.print("We apply HYPOTHESIS to %a with induction hypothesis %a and substitution %a.  ",
      _equ.getName(), _hypothesisName, _helper.substitutionPrintable(_equ.getRenaming()));
    if (_requirement.isEmpty()) {
      module.print("This does not cause any new ordering requirements to be imposed.");
    }
    else {
      module.print("To this end, we impose the requirement that %a.", _requirement.get());
    }
    if (_doneAfter) {
      module.println("  Since the left-hand side and right-hand side of the resulting equation " +
        "are equal, we immediately apply DELETE to remove it.");
    }
    else module.println();
  }
}

