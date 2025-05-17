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
      new ConstrainedReductionHelper(left, right, hequ.getConstraint(), hypo.getRenamingCopy(),
                                     "induction hypothesis", proof, pos, subst);
    EquationContext original = proof.getProofState().getTopEquation();
    if (!helper.extendSubstitutionBasic(m)) return Optional.empty();
    helper.extendSubstitutionWithConstraintDefinitions();
    if (!helper.checkEverythingSubstituted(m)) return Optional.empty();

    Pair<Equation,Renaming> neweqdata = helper.reduce();
    Equation neweq = neweqdata.fst();
    Renaming newrenaming = neweqdata.snd();
    ArrayList<OrdReq> requirements = new ArrayList<OrdReq>();

    int id = proof.getProofState().getLastUsedIndex() + 1;
    EquationContext result = generateResultEquationContext(original, pos, neweq, newrenaming,
                                                           id, requirements);
    if (result == null) {
      m.ifPresent(o -> o.println("The hypothesis cannot be applied, as it would cause an " +
        "obviously unsatisfiable ordering requirement to be imposed."));
      return Optional.empty();
    }
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
                                                               Renaming newrenaming, int index,
                                                               ArrayList<OrdReq> reqs) {
    // • is greater than anything, so if • occurs on any side, we can keep it as the only greater
    // term in the resulting equation
    if (original.getLeftGreaterTerm().isEmpty() || original.getRightGreaterTerm().isEmpty()) {
      return new EquationContext(neweq, index, newrenaming);
    }

    // otherwise, let's write the equation as (s', C[lγ] -><- t | φ, t') or (t', t -> C[lγ] | φ, s')
    Term lgamma = original.getEquation().querySubterm(pos);
    Term rgamma = neweq.querySubterm(pos);
    Term phi = neweq.getConstraint();
    Term sprime, tprime;
    if (pos.querySide() == EquationPosition.Side.Left) {
      sprime = original.getLeftGreaterTerm().get();
      tprime = original.getRightGreaterTerm().get();
    }
    else {
      sprime = original.getRightGreaterTerm().get();
      tprime = original.getLeftGreaterTerm().get();
    }
    
    // if s' = lγ, then clearly we do not have s' ≻ lγ, so we need t' ≻ lγ = s', and hence can
    // safely continue with greater terms {t',t'}
    if (sprime.equals(lgamma)) {
      if (tprime.equals(lgamma) || tprime.equals(rgamma)) return null;
      reqs.add(new OrdReq(tprime, lgamma, phi, newrenaming));
      reqs.add(new OrdReq(tprime, rgamma, phi, newrenaming));
      return new EquationContext(tprime, neweq, tprime, index, newrenaming);
    }

    // in all other cases, we impose the requirement that s' ≻ lγ
    reqs.add(new OrdReq(sprime, lgamma, phi, newrenaming));

    // The only remaining question is whether s' ≻ rγ or t' ≻ rγ.  For this, we impose the
    // following heuristic: of course if one of them is equal to rγ we choose the other, and if
    // C[rγ] = t we in principle choose t' ≻ rγ; otherwise we let s' ≻ rγ (since the proof of the
    // equation is not yet almost-finished, and we will continue with (s',t'))
    if (neweq.getLhs().equals(neweq.getRhs())) {
      if (!tprime.equals(rgamma)) reqs.add(new OrdReq(tprime, rgamma, phi, newrenaming));
      else if (sprime.equals(rgamma)) return null;
      else reqs.add(new OrdReq(sprime, rgamma, phi, newrenaming));
    }

    else {
      if (!sprime.equals(rgamma)) reqs.add(new OrdReq(sprime, rgamma, phi, newrenaming));
      else if (tprime.equals(rgamma)) return null;
      else reqs.add(new OrdReq(tprime, rgamma, phi, newrenaming));
    }

    return original.replace(neweq, newrenaming, index);
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

