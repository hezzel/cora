/**************************************************************************************************
 Copyright 2024-2025 Cynthia Kop

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
import charlie.util.Pair;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import charlie.theorytranslation.TermSmtTranslator;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/** The deduction command for simplifying an equation with a Rule */
public final class DeductionSimplify extends DeductionStep {
  private ConstrainedReductionHelper _helper;
  private String _ruleName;

  /** Private constructor, called (only) by createStep */
  private DeductionSimplify(ProofState state, ProofContext context, String ruleName,
                            ConstrainedReductionHelper h) {
    super(state, context);
    _helper = h;
    _ruleName = ruleName;
  }

  /**
   * Creates a simplification step for the given information, checking that there is indeed a
   * match but NOT that the constraint is satisfied or that no new variables are created.
   * The substitution will not be altered, and does not become the property of the step; it is
   * safe to change afterwards.
   */
  public static DeductionSimplify createStep(PartialProof proof, Optional<OutputModule> m,
                                             String ruleName, EquationPosition pos,
                                             Substitution subst) {
    Rule rule = proof.getContext().getRule(ruleName);
    if (rule == null) {
      m.ifPresent(o -> o.println("No such rule: %a.", ruleName));
      return null;
    }

    ConstrainedReductionHelper helper =
      new ConstrainedReductionHelper(rule.queryLeftSide(), rule.queryRightSide(),
        rule.queryConstraint(), proof.getContext().getRenaming(ruleName), "rule", proof, pos,
        subst);
    
    if (!helper.extendSubstitutionBasic(m)) return null;
    helper.makePreAlter();

    return new DeductionSimplify(proof.getProofState(), proof.getContext(), ruleName, helper);
  }

  /**
   * This function checks if we can indeed apply the rule l → r | φ with the substitution γ to the
   * equation C[lγ]_p ≈ t | ψ, with data as given by step.  Note that, for a step to be created, it
   * is already given that l γ is indeed the subterm at the given position of the equation.  Hence,
   * the remaining checks are:
   * - check that all (meta-)vars in the rule are in dom(δ)
   * - check that ψ ⇒ φδ is valid
   */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    if (_helper.constraintIsTrue()) return true;
    DeductionAlterDefinitions dad = _helper.queryPreAlter();
    if (dad != null && !dad.verify(module)) return false;
    if (!_helper.checkEverythingSubstituted(module)) return false;
    Term constraint = _equ.getEquation().getConstraint();
    return _helper.checkConstraintGoodForReduction(module, Settings.smtSolver);
  }

  @Override
  protected ProofState tryApply(Optional<OutputModule> module) {
    Pair<Equation,Renaming> pair = _helper.reduce();
    EquationContext ec = _equ.replace(pair.fst(), pair.snd(), _state.getLastUsedIndex() + 1);
    return _state.replaceTopEquation(ec);
  }

  @Override
  public String commandDescription() {
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add("simplify ", _ruleName, " ", _helper.queryPosition(), " with ",
      _helper.substitutionPrintable(_equ.getRenamingCopy()));
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    DeductionAlterDefinitions prestep = _helper.queryPreAlter();
    if (prestep == null) module.print("We apply SIMPLIFICATION to %a", _equ.getName());
    else {
      module.print("We apply ALTER to add %a to the constraint of %a, and then we apply " +
        "SIMPLIFICATION to the resulting equation",
        Printer.makePrintable(prestep.queryAddedConstraint(), prestep.queryUpdatedRenaming()),
        _equ.getName());
    }
    module.println(" with rule %a and substitution %a.",
      _ruleName, _helper.substitutionPrintable(_equ.getRenamingCopy()));
  }
}

