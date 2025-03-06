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

import java.util.ArrayList;
import java.util.Optional;
import charlie.terms.*;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/** The deduction command for simplifying an equation with an induction hypothesis */
public final class DeductionHypothesis extends DeductionStep {
  private ConstrainedReductionHelper _helper;
  private String _hypothesisName;
  private boolean _inversed;
  private ArrayList<OrdReq> _requirements;
  private EquationContext _result;

  /** Private constructor, called (only) by createStep */
  private DeductionHypothesis(ProofState state, ProofContext context, String hypoName,
                            boolean inverse, ConstrainedReductionHelper h,
                            EquationContext result, ArrayList<OrdReq> reqs) {
    super(state, context);
    _helper = h;
    _hypothesisName = hypoName;
    _inversed = inverse;
    _result = result;
    _requirements = reqs;
  }

  /**
   * Creates a simplification-with-hypothesis step for the given information, checking that there
   * is indeed a match but NOT that the constraint is satisfied.
   * The substitution will not be altered, and does not become the property of the step; it is
   * safe to change afterwards.
   * For now, the step decides for itself which ordering requirement is imposed; the user cannot
   * indicate this.  This may be changed in the future, though.
   */
  public static Optional<DeductionHypothesis> createStep(PartialProof proof, Optional<OutputModule> m,
                                                         Hypothesis hypo, boolean inverse,
                                                         EquationPosition pos, Substitution subst) {
    Equation hequ = hypo.getEquation();
    Term left = inverse ? hequ.getRhs() : hequ.getLhs();
    Term right = inverse ? hequ.getLhs() : hequ.getRhs();

    ConstrainedReductionHelper helper =
      new ConstrainedReductionHelper(left, right, hequ.getConstraint(), hypo.getRenaming(), pos,
                                     subst, "induction hypothesis");
    EquationContext original = proof.getProofState().getTopEquation();
    if (!helper.extendSubstitution(original.getEquation(), m)) return Optional.empty();
    if (!helper.checkEverythingSubstituted(m)) return Optional.empty();

    Equation neweq = helper.reduce(original.getEquation(), m);
    ArrayList<OrdReq> requirements = new ArrayList<OrdReq>();

    int id = proof.getProofState().getLastUsedIndex() + 1;
    EquationContext result = generateResultEquationContext(original, pos, neweq, id, requirements);
    return Optional.of(new DeductionHypothesis(proof.getProofState(), proof.getContext(),
                                               hypo.getName() + (inverse ? "^{-1}" : ""), inverse,
                                               helper, result, requirements));
  }

  /**
   * Helper function for createStep: given that original is reduced at position pos, and this
   * results in the equation neweq, this function determines the equation context for neweq (so in
   * particular the two new greater terms), and adds the corresponding ordering requirements to
   * the given list.
   */
  private static EquationContext generateResultEquationContext(EquationContext original,
                                                               EquationPosition pos, Equation neweq,
                                                               int index, ArrayList<OrdReq> reqs) {
    // • is greater than anything, so if • occurs on any side, we can keep it as the only greater
    // term in the resulting equation
    if (original.getLeftGreaterTerm().isEmpty() || original.getRightGreaterTerm().isEmpty()) {
      return new EquationContext(neweq, index, original.getRenaming());
    }

    // Otherwise, suppose we are rewriting (s', C[lγ] -><- t | φ, t'); the case for a reduction in
    // the right-hand side is symmetric.  We will continue with (s', C[rγ] -><- t | φ, t') except
    // in two special cases, which also change the ordering requirements imposed:
    // A: s' = lγ
    // B: C[rγ] = t and t' != rγ
    // we require s' ≻ lγ except in CASE A; there, we require t' ≻ lγ instead
    // we require s' ≻ rγ except in CASE A or CASE B; there, we require t' ≻ rγ instead
    // if CASE A or CASE B applies, we instead continue with (t', C[rγ] -><- t | φ, t')
    Term lgamma = original.getEquation().querySubterm(pos);
    Term rgamma = neweq.querySubterm(pos);
    Term phi = neweq.getConstraint();
    Renaming ren = original.getRenaming();
    Term sprime, tprime;
    if (pos.querySide() == EquationPosition.Side.Left) {
      sprime = original.getLeftGreaterTerm().get();
      tprime = original.getRightGreaterTerm().get();
    }
    else {
      sprime = original.getRightGreaterTerm().get();
      tprime = original.getLeftGreaterTerm().get();
    }
    boolean caseA = sprime.equals(lgamma);
    boolean caseB = neweq.getLhs().equals(neweq.getRhs()) && !tprime.equals(rgamma);
    if (caseA) reqs.add(new OrdReq(tprime, lgamma, phi, ren));
    else reqs.add(new OrdReq(sprime, lgamma, phi, ren));
    if (caseA || caseB) sprime = tprime;
    reqs.add(new OrdReq(sprime, rgamma, phi, ren));
    EquationContext result;
    if (pos.querySide() == EquationPosition.Side.Left) {
      return new EquationContext(sprime, neweq, tprime, index, ren);
    }
    else {
      return new EquationContext(tprime, neweq, sprime, index, ren);
    }
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
    ProofState tmp = _state;
    for (OrdReq req : _requirements) tmp = tmp.addOrderingRequirement(req);
    return tmp.replaceTopEquation(_result);
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
    if (_requirements.size() == 0) {
      module.println("This does not cause any new ordering requirements to be imposed.");
    }
    else {
      module.print("To this end, we impose the requirements that ");
      for (int i = 0; i < _requirements.size(); i++) {
        if (i == _requirements.size()-1) module.print(" and ");
        else if (i != 0) module.print(", ");
        module.print("%a", _requirements.get(i));
      }
      module.println(".");
    }
  }
}

