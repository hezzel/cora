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
import charlie.terms.Renaming;
import charlie.terms.Substitution;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

public final class DeductionPostulate extends DeductionStep {
  private Equation _equation;
  private Renaming _renaming;

  private DeductionPostulate(ProofState state, ProofContext context, Equation equ, Renaming ren) {
    super(state, context);
    _equation = equ;
    _renaming = ren;
  }
 
  /**
   * Returns an Optional to be in line with other deduction steps, even though there is (at this
   * time) no way for the step creation to fail.
   */
  public static Optional<DeductionPostulate> createStep(PartialProof proof,
                                                        Optional<OutputModule> module,
                                                        Equation equ, Renaming ren) {
    ProofState state = proof.getProofState();
    return Optional.of(new DeductionPostulate(proof.getProofState(), proof.getContext(), equ, ren));
  }

  @Override
  public boolean verify(Optional<OutputModule> module) {
    return true;
  }

  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    EquationContext n = new EquationContext(_equation, _state.getLastUsedIndex() + 1, _renaming);
    return _state.addEquation(n);
  }

  @Override
  public String commandDescription() {
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add("postulate ", _equation.makePrintableWith(_renaming));
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    module.println("We apply POSTULATE to add the lemma equation %a to the current proof state.",
      _equation.makePrintableWith(_renaming));
  }
}

