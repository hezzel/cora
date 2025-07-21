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
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.Renaming;
import charlie.terms.Substitution;
import charlie.printer.Printer;
import charlie.theorytranslation.TermAnalyser;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

public final class DeductionDelete extends DeductionStep {
  private boolean _bothSidesEqual;

  private DeductionDelete(ProofState state, ProofContext context, boolean equalsides) {
    super(state, context);
    _bothSidesEqual = equalsides;
  }
 
  public static DeductionDelete createStep(PartialProof proof, Optional<OutputModule> module) {
    ProofState state = proof.getProofState();
    Equation eq = DeductionStep.getTopEquation(state, module);
    if (eq == null) return null;
    // option 1: both sides are equal
    if (eq.getLhs().equals(eq.getRhs())) {
      return new DeductionDelete(state, proof.getContext(), true);
    }
    // option 2: we will have to check the constraint
    return new DeductionDelete(state, proof.getContext(), false);
  }

  /**
   * Do all the heavy checks required before executing a step.  Since a DeductionDelete can only be
   * created through createStep, we may assume that the proof state is non-empty, so there is in
   * fact an equation to delete.
   */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    if (_bothSidesEqual) return true; // nothing to check
    Term constraint = _equ.getEquation().getConstraint();
    switch (TermAnalyser.satisfy(constraint, Settings.smtSolver)) {
      case TermAnalyser.Result.MAYBE(String reason):
        println(module, "The DELETE rule is not obviously applicable: the left- and right-hand " +
          "side are not the same, and checking satisfiability returns MAYBE (%a)", reason);
        return false;
      case TermAnalyser.Result.YES(Substitution val):
        Renaming renaming = _equ.getRenamingCopy();
        println(module, "The DELETE rule is not applicable: the left- and right-hand side are " +
          "not the same, and the constraint is satisfiable using substitution %a.",
          Printer.makePrintable(val, renaming, renaming));
    return false;
      case TermAnalyser.Result.NO(): return true;
    }
  }

  /** Try to apply the deduction rule to the current proof state */
  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    return _state.deleteTopEquation();
  }

  @Override
  public String commandDescription() {
    return "delete";
  }

  @Override
  public void explain(OutputModule module) {
    module.println("We apply DELETION to %a because %a.  " +
      "Thus, we may remove this equation from the proof state.", _equ.getName(),
      _bothSidesEqual ? "both sides are equal" : "the constraint is unsatisfiable");
  }
}

