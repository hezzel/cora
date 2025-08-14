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
import charlie.util.Pair;
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
   * For now, the step decides for itself which ordering requirements are imposed; the user cannot
   * indicate this.  This may be changed in the future, though.
   */
  public static DeductionHypothesis createStep(PartialProof proof, Optional<OutputModule> m,
                                               Hypothesis hypo, boolean inverse,
                                               EquationPosition pos, Substitution subst) {
    Equation hequ = hypo.getEquation();
    Term left = inverse ? hequ.getRhs() : hequ.getLhs();
    Term right = inverse ? hequ.getLhs() : hequ.getRhs();

    ConstrainedReductionHelper helper =
      new ConstrainedReductionHelper(left, right, hequ.getConstraint(), hypo.getRenamingCopy(),
                                     "induction hypothesis", proof, pos, subst);
    EquationContext original = proof.getProofState().getTopEquation();
    if (!helper.extendSubstitutionBasic(m)) return null;
    helper.extendSubstitutionWithConstraintDefinitions();
    if (!helper.checkEverythingSubstituted(m)) return null;

    Pair<Equation,Renaming> neweqdata = helper.reduce();
    Equation neweq = neweqdata.fst();
    Renaming newrenaming = neweqdata.snd();
    ArrayList<OrdReq> requirements = new ArrayList<OrdReq>();

    if (!checkOrderingRequirements(original, pos, neweq, newrenaming, requirements)) {
      m.ifPresent(o -> o.println("The hypothesis cannot be applied, as it would cause an " +
        "obviously unsatisfiable ordering requirement to be imposed."));
      return null;
    }
    int id = proof.getProofState().getLastUsedIndex() + 1;
    EquationContext result = new EquationContext(original.getLeftGreaterTerm(), neweq,
                                                 original.getRightGreaterTerm(), id, newrenaming);
    return new DeductionHypothesis(proof.getProofState(), proof.getContext(),
                                   hypo.getName() + (inverse ? "^{-1}" : ""),
                                   inverse, helper, result, requirements);
  }

  /**
   * Helper function for createStep: given that original is reduced at position pos, and this
   * results in the equation neweq, this function determines the ordering requirements, if any,
   * that need to be imposed for this hypothesis step to be applied, and returns true if it is
   * possible that they might be successful.  If they cannot be successful, false is returned.
   */
  private static boolean checkOrderingRequirements(EquationContext original,
                                                   EquationPosition pos, Equation neweq,
                                                   Renaming newrenaming, ArrayList<OrdReq> reqs) {
    // • is greater than anything, so if • occurs on both sides, there's nothing to require
    if (original.getLeftGreaterTerm().isEmpty() && original.getRightGreaterTerm().isEmpty()) {
      return true;
    }

    // to start, let's write the equation as (s', C[lγ] -><- t | φ, t') or (t', t -> C[lγ] | φ, s')
    Term sprime = null, tprime = null, s, q, t;
    if (pos.querySide() == EquationPosition.Side.Left) {
      if (!original.getLeftGreaterTerm().isEmpty()) sprime = original.getLeftGreaterTerm().get();
      if (!original.getRightGreaterTerm().isEmpty()) tprime = original.getRightGreaterTerm().get();
      s = original.getEquation().getLhs();
      q = neweq.getLhs();
      t = original.getEquation().getRhs();
    }
    else {
      if (!original.getRightGreaterTerm().isEmpty()) sprime = original.getRightGreaterTerm().get();
      if (!original.getLeftGreaterTerm().isEmpty()) tprime = original.getLeftGreaterTerm().get();
      s = original.getEquation().getRhs();
      q = neweq.getRhs();
      t = original.getEquation().getLhs();
    }

    // given (s', C[lγ] -><- t | φ, t'), we require one of the following to ensure that
    // {s',t'} ≻{mul} {l γ, r γ} and the result is still a bounded equation context:
    // [A] s' ≻ l γ and s' ≻ r γ and s' ≽ q = C[rγ]
    // [B] t' ≻ r γ and s' ≽ q = C[rγ]
    if (sprime == null) return true; // case [A] clearly holds if s' = •
    boolean sequalq = sprime.equals(q);
    Term lgamma = original.getEquation().querySubterm(pos);
    Term phi = neweq.getConstraint();
    // in both cases, s' ≽ q must hold, and since we don't have s = q, let's require s ≻ q
    if (!sequalq) reqs.add(new OrdReq(sprime, q, phi, newrenaming));
    // if case [A] is possible, then go for that
    if (!sprime.equals(lgamma)) { // since s' ≽ C[lγ] ≽ lγ, this implies s' ≻ lγ directly
      if (!sequalq) return true;  // we have already required s' ≻ q ≽ rγ
      if (!pos.queryPosition().isEmpty()) return true; // we have s' = C[rγ] ≻ rγ
    }
    // otherwise, go for case [B]; note that this can only occur if C is the empty context, so
    // rγ = q
    if (tprime.equals(q)) return false;
    reqs.add(new OrdReq(tprime, q, phi, newrenaming));
    return true;
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
    // it needs to be an innermost step if we're using innermost strategy
    if ( (Settings.queryRewritingStrategy().equals(Settings.Strategy.Innermost) ||
          Settings.queryRewritingStrategy().equals(Settings.Strategy.CallByValue)) &&
         !_helper.checkInnermost()) return false;
    // the constraint implication should be satisfied
    if (_helper.constraintIsTrue()) return true;
    return _helper.checkConstraintGoodForReduction(module, Settings.smtSolver);
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
      _helper.substitutionPrintable(_equ.getRenamingCopy()));
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    module.print("We apply HYPOTHESIS to %a with induction hypothesis %a and substitution %a.  ",
      _equ.getName(), _hypothesisName, _helper.substitutionPrintable(_equ.getRenamingCopy()));
    if (_requirements.size() == 0) {
      module.println("This does not cause any new ordering requirements to be imposed.");
    }
    else if (_requirements.size() == 1) {
      module.println("To this end, we impose the requirement that %a.", _requirements.get(0));
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

