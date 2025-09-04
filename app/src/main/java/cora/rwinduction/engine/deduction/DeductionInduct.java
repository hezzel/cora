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
import charlie.util.FixedList;
import charlie.terms.Term;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

public final class DeductionInduct extends DeductionStep {
  private DeductionInduct(ProofState state, ProofContext context) {
    super(state, context);
  }

  public static DeductionInduct createStep(PartialProof proof, Optional<OutputModule> m) {
    ProofState state = proof.getProofState();
    if (state.isFinalState()) {
      m.ifPresent( o -> o.println("The proof is already complete.") );
      return null;
    }
    return new DeductionInduct(state, proof.getContext());
  }

  @Override
  public boolean verify(Optional<OutputModule> module) {
    // check that we don't already have this induction hypothesis!
    for (Hypothesis hypo : _state.getHypotheses()) {
      if (hypo.getEquation() == _equ.getEquation()) {
        module.ifPresent(o -> o.println("You already have this induction hypothesis (%a), so " +
          "there is no benefit to using INDUCT again on this equation.", hypo.getName()));
        return false;
      }
    }
    return true;
  }

  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    Hypothesis hypothesis = new Hypothesis(_equ.getEquation(), _equ.getIndex(),
                                           _equ.getRenaming());
    // special case: the equation context was already (s, s = t | φ, t); in this case the ec stays
    // the same, but the hypothesis *is* added
    if (!_equ.getLeftGreaterTerm().isEmpty() && !_equ.getRightGreaterTerm().isEmpty() &&
        _equ.getLeftGreaterTerm().get().equals(_equ.getEquation().getLhs()) &&
        _equ.getRightGreaterTerm().get().equals(_equ.getEquation().getRhs())) {
      return _state.addHypothesis(hypothesis);
    }

    int index = _state.getLastUsedIndex() + 1;
    Equation equation = _equ.getEquation();
    EquationContext newequ = new EquationContext(equation.getLhs(), equation,
      equation.getRhs(), index, _equ.getRenaming());
    FixedList.Builder<EquationContext> ecbuilder = new FixedList.Builder<EquationContext>();
    for (EquationContext ec : _state.getEquations()) {
      if (ec == _equ) ecbuilder.add(newequ);
      else ecbuilder.add(ec);
    }

    FixedList<EquationContext> newEquations = ecbuilder.build();
    FixedList<Hypothesis> newHypotheses = _state.getHypotheses().append(hypothesis);

    return new ProofState(newEquations, newHypotheses, _state.getOrderingRequirements(),
                          _state.getIncompleteEquations(), index);
  }

  @Override
  public String commandDescription() {
    return "induct";
  }

  @Override
  public void explain(OutputModule module) {
    module.println("We apply INDUCT to %a, which causes %a to be added to the set H of induction " +
      "hypotheses.", _equ.getName(),
      _equ.getEquation().makePrintableWith(_equ.getRenaming()));
  }
}

