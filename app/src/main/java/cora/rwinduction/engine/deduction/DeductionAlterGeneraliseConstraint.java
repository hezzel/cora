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
import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.Renaming;
import charlie.terms.Term;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import charlie.theorytranslation.TermSmtTranslator;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/**
 * This deduction step handles both the "alter constraint" and "generalise constraint" commands,
 * creating a step that replaces the constraint by an equivalent or implied constraint respectively.
 */
public final class DeductionAlterGeneraliseConstraint extends DeductionStep {
  private Term _originalConstraint;
  private Term _newConstraint;
  private boolean _alters;  // if false, this is ALTER; if false, it is GENERALISE

  private DeductionAlterGeneraliseConstraint(ProofState state, ProofContext context,
                                             Term original, Term update, boolean isAlter) {
    super(state, context);
    _originalConstraint = original;
    _newConstraint = update;
    _alters = isAlter;
  }

  /**
   * Helper function for both create<...>Step functions: this ensures that no variables occur in
   * newConstraint that are not known in the original equationContext, and gives an error message
   * if this condition is not satisfied.  
   */
  private static boolean checkNoFreshVariables(EquationContext original, Term newConstraint,
                                               String cmd, Optional<OutputModule> module) {
    Renaming renaming = original.getRenaming();
    for (Replaceable x : newConstraint.freeReplaceables()) {
      if (renaming.getName(x) == null) {
        module.ifPresent(o -> o.println("Fresh occurrence of " + x.queryName() + " is not " +
          "allowed in this application of the " + cmd + " command (use ALTER ADD to add new " +
          "variables to the constraint)."));
        return false;
      }
    }
    return true;
  }

  /**
   * Creates a step to replace the constraint by the given EQUIVALENT one.  This fails if the new
   * constraint uses any variables that did not occur in the existing equation context.
   */
  public static DeductionAlterGeneraliseConstraint createAlterStep(PartialProof proof,
                                                                   Optional<OutputModule> module,
                                                                   Term newConstraint) {
    ProofState state = proof.getProofState();
    EquationContext original = state.getTopEquation();
    if (!checkNoFreshVariables(original, newConstraint, "ALTER", module)) return null;
    return new DeductionAlterGeneraliseConstraint(state, proof.getContext(),
                                                  original.getEquation().getConstraint(),
                                                  newConstraint, true);
  }

  /**
   * Creates a step to replace the constraint by the given IMPLIED one.  This fails if the new
   * constraint uses any variables that did not occur in the existing equation context.
   */
  public static DeductionAlterGeneraliseConstraint createGeneraliseStep(PartialProof proof,
                                                                        Optional<OutputModule> mod,
                                                                        Term newConstraint) {
    ProofState state = proof.getProofState();
    EquationContext original = state.getTopEquation();
    if (!checkNoFreshVariables(original, newConstraint, "GENERALISE", mod)) return null;
    return new DeductionAlterGeneraliseConstraint(state, proof.getContext(),
                                                  original.getEquation().getConstraint(),
                                                  newConstraint, false);
  }

  private String queryCommandName(boolean capitalise) {
    if (_alters) {
      if (capitalise) return "ALTER";
      else return "alter";
    }
    else {
      if (capitalise) return "GENERALISE";
      else return "generalise";
    }
  }

  /** Before executing this step, we should check if the new constraint is implied / equivalent. */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    TermSmtTranslator translator = new TermSmtTranslator();
    translator.requireImplication(_originalConstraint, _newConstraint);
    if (_alters) translator.requireImplication(_newConstraint, _originalConstraint);
    if (Settings.smtSolver.checkValidity(translator.queryProblem())) return true;
    module.ifPresent(o -> o.println("It is not obvious if this usage of " +
      queryCommandName(false) + " is permitted: I could not prove that %a " +
      (_alters ? "%{iff}" : "%{implies}") + " %a.",
      Printer.makePrintable(_originalConstraint, _state.getTopEquation().getRenaming()),
      Printer.makePrintable(_newConstraint, _state.getTopEquation().getRenaming())));
    return false;
  }

  /** Apply the deduction rule to the current proof state */
  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    Equation oldEquation = _state.getTopEquation().getEquation();
    Equation newEquation = new Equation(oldEquation.getLhs(), oldEquation.getRhs(), _newConstraint);
    int newIndex = _state.getLastUsedIndex()+1;
    ProofState ret =
      _state.replaceTopEquation(_state.getTopEquation().replace(newEquation, newIndex));
    if (!_alters) ret = ret.setIncomplete(newIndex);
    return ret;
  }

  @Override
  public String commandDescription() {
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add(queryCommandName(false) + " constraint ");
    printer.add(printer.makePrintable(_newConstraint, _state.getTopEquation().getRenaming()));
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    module.println("We apply %a to replace the constraint of %a by %a.", queryCommandName(true),
      _equ.getName(), Printer.makePrintable(_newConstraint, _state.getTopEquation().getRenaming()));
  }
}

