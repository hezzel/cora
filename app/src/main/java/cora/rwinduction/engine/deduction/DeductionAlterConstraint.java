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
import charlie.terms.Replaceable;
import charlie.terms.Term;
import charlie.terms.Renaming;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import charlie.theorytranslation.TermSmtTranslator;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/** The variant of Alter that is used to change the constraint to an equivalent one. */
public final class DeductionAlterConstraint extends DeductionStep {
  private Term _originalConstraint;
  private Term _newConstraint;
  private Renaming _renaming;
    // _renaming is just a copy of the original equation's renaming, but we store this to avoid
    // needless copying

  /** Creates the step. */
  private DeductionAlterConstraint(ProofState state, ProofContext context, Term original,
                                   Term update, Renaming renaming) {
    super(state, context);
    _originalConstraint = original;
    _newConstraint = update;
    _renaming = renaming;
  }

  /**
   * Creates a step to replace the constraint by the given one.  This fails if the new constraint
   * uses any variables that did not occur in the existing equation context.
   */
  public static DeductionAlterConstraint createStep(PartialProof proof,
                                                    Optional<OutputModule> module,
                                                    Term newConstraint) {
    ProofState state = proof.getProofState();
    EquationContext original = state.getTopEquation();
    Renaming renaming = original.getRenamingCopy();
    for (Replaceable x : newConstraint.freeReplaceables()) {
      if (renaming.getName(x) == null) {
        module.ifPresent(o -> o.println("Fresh occurrence of " + x.queryName() + " is not " +
          "allowed in this application of the ALTER command (use alter ADD to add new variables " +
          "to the constraint)."));
        return null;
      }
    }
    return new DeductionAlterConstraint(state, proof.getContext(),
                                        original.getEquation().getConstraint(),
                                        newConstraint, renaming);
  }

  /** Before executing this alteration, we do not check if the constraints are indeed equivalent! */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    TermSmtTranslator translator = new TermSmtTranslator();
    translator.requireImplication(_originalConstraint, _newConstraint);
    translator.requireImplication(_newConstraint, _originalConstraint);
    if (Settings.smtSolver.checkValidity(translator.queryProblem())) return true;
    module.ifPresent(o -> o.println("It is not obvious if this usage of alteration is permitted: " +
      "I could not prove that %a %{iff} %a.",
      Printer.makePrintable(_originalConstraint, _renaming),
      Printer.makePrintable(_newConstraint, _renaming)));
    return false;
  }

  /** Apply the deduction rule to the current proof state */
  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    Equation oldEquation = _state.getTopEquation().getEquation();
    Equation newEquation = new Equation(oldEquation.getLhs(), oldEquation.getRhs(), _newConstraint);
    return _state.replaceTopEquation(_state.getTopEquation().replace(newEquation, _renaming,
                                                                     _state.getLastUsedIndex()+1));
  }

  @Override
  public String commandDescription() {
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add("alter constraint ");
    printer.add(printer.makePrintable(_newConstraint, _renaming));
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    module.println("We apply ALTER to replace the constraint of %a by %a.",
      _equ.getName(), Printer.makePrintable(_newConstraint, _renaming));
  }
}

