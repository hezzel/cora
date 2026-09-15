/**************************************************************************************************
 Copyright 2026 Cynthia Kop

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
import charlie.terms.replaceable.Renaming;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.substitution.MutableSubstitution;
import charlie.theory.Theory;
import charlie.theory.TheoryFactory;
import charlie.theorytranslation.TermSmtTranslator;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/**
 * The variant of Alter that is only used to change a into either another variable or a value, if
 * the constraint implies that they are the same.
 */
public final class DeductionAlterObserve extends DeductionStep {
  private Variable _original;
  private Term _replacement;

  /** Creates the step */
  private DeductionAlterObserve(ProofState state, ProofContext context,
                                Variable original, Term replacement) {
    super(state, context);
    _original = original;
    _replacement = replacement;
  }

  /**
   * Creates a step to do the given alteration, or returns null if that fails.
   *
   * This will succeed if replacement is a value of the same theory sort as original, and original
   * actually occurs in the left- or right-hand side of the equation.
   */
  public static DeductionAlterObserve createStep(PartialProof proof, Optional<OutputModule> module,
                                                 Variable original, Term replacement) {
    ProofState state = proof.getProofState();

    if (!original.queryType().isBaseType() ||
        !Theory.isTheory(original.queryType())) {
      module.ifPresent(o -> o.println("The input type should be a theory sort, but is %a.",
        original.queryType()));
      return null;
    }
    if (!original.queryType().equals(replacement.queryType())) {
      module.ifPresent(o -> o.println("Both sides of the observed equality should have the same " +
        "type (given: %a versus %a).", original.queryType(), replacement.queryType()));
      return null;
    }
    if (!replacement.isVariable() && !Theory.isValue(replacement)) {
      Renaming renaming = state.getTopEquation().getRenaming();
      module.ifPresent(o -> o.println("Replacement in ALTER OBSERVE should be a variable or " +
        "value; %a is neither!", Printer.makePrintable(replacement, renaming)));
      return null;
    }
    if (!state.getTopEquation().getLhs().queryFreeReplaceables().contains(original) &&
        !state.getTopEquation().getRhs().queryFreeReplaceables().contains(original)) {
      Renaming renaming = state.getTopEquation().getRenaming();
      module.ifPresent(o -> o.println("Variable %a does not occur in the left- or right-hand " +
        "side of the equation!", renaming.getName(original)));
      return null;
    }

    return new DeductionAlterObserve(state, proof.getContext(), original, replacement);
  }

  /** Check that the constraint implies that original = replacement! */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    TermSmtTranslator translator = new TermSmtTranslator();
    Term constraint = _state.getTopEquation().getConstraint();
    Term equal = TheoryFactory.createEquality(_original, _replacement);
    translator.requireImplication(constraint, equal);
    if (Settings.smtSolver.checkValidity(translator.queryProblem())) return true;
    module.ifPresent(o -> o.println("It is not obvious if this usage of alteration is permitted: " +
      "I could not prove that %a %{implies} %a.",
      Printer.makePrintable(constraint, _state.getTopEquation().getRenaming()),
      Printer.makePrintable(equal, _state.getTopEquation().getRenaming())));
    return false;
  }

  /** Apply the deduction rule to the current proof state */
  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    MutableSubstitution subst = new MutableSubstitution(_original, _replacement);
    Term newleft = _state.getTopEquation().getLhs().substitute(subst);
    Term newright = _state.getTopEquation().getRhs().substitute(subst);
    Equation neweq = new Equation(newleft, newright, _state.getTopEquation().getConstraint());
    return _state.replaceTopEquation(_state.getTopEquation().replace(neweq,
      _state.getLastUsedIndex() + 1));
  }

  @Override
  public String commandDescription() {
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add("alter observe ");
    printer.add(Printer.makePrintable(_original, _state.getTopEquation().getRenaming()));
    printer.add(" = ");
    printer.add(Printer.makePrintable(_replacement, _state.getTopEquation().getRenaming()));
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    module.println("We apply ALTER to replace %a in the left- and right-hand side of the " +
      "equation by %a.", Printer.makePrintable(_original, _state.getTopEquation().getRenaming()),
      Printer.makePrintable(_replacement, _state.getTopEquation().getRenaming()));
  }
}

