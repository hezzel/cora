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
import charlie.terms.Renaming;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

public final class DeductionInduct extends DeductionStep {
  private ArrayList<OrdReq> _requirements;

  private DeductionInduct(ProofState state, ProofContext context, ArrayList<OrdReq> reqs) {
    super(state, context);
    _requirements = reqs;
  }

  public static Optional<DeductionInduct> createStep(PartialProof proof, Optional<OutputModule> m) {
    ProofState state = proof.getProofState();
    if (state.isFinalState()) {
      m.ifPresent( o -> o.println("The proof is already complete.") );
      return Optional.empty();
    }
    ArrayList<OrdReq> reqs = new ArrayList<OrdReq>();
    EquationContext context = state.getTopEquation();
    Equation eq = context.getEquation();
    Optional<Term> lterm = context.getLeftGreaterTerm();
    if (!lterm.isEmpty() && !lterm.get().equals(eq.getLhs())) {
      reqs.add(new OrdReq(lterm.get(), eq.getLhs(), eq.getConstraint(),
                          context.getRenaming(), false));
    }
    Optional<Term> rterm = context.getRightGreaterTerm();
    if (!rterm.isEmpty() && !rterm.get().equals(eq.getLhs())) {
      reqs.add(new OrdReq(rterm.get(), eq.getRhs(), eq.getConstraint(),
                          context.getRenaming(), false));
    }
    return Optional.of(new DeductionInduct(state, proof.getContext(), reqs));
  }

  @Override
  public boolean verify(Optional<OutputModule> module) {
    // in the future we may want to do an actual termination check already at this point
    return true;
  }

  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    Hypothesis hypothesis = new Hypothesis(_equ.getEquation(), _equ.getIndex(), _equ.getRenaming());
    // special case: the equation context was already (s, s = t | φ, t); in this case the ec stays
    // the same, and there are no requirements, but the hypothesis *is* added
    if (_requirements.size() == 0 && !_equ.getLeftGreaterTerm().isEmpty() &&
                                     !_equ.getRightGreaterTerm().isEmpty()) {
      return _state.addHypothesis(hypothesis);
    }

    int index = _state.getLastUsedIndex() + 1;
    Equation equation = _equ.getEquation();
    EquationContext newequ = new EquationContext(equation.getLhs(),
      new Equation(equation.getLhs(), equation.getRhs(), equation.getConstraint()),
      equation.getRhs(), index, _equ.getRenaming());
    FixedList.Builder<EquationContext> ecbuilder = new FixedList.Builder<EquationContext>();
    for (EquationContext ec : _state.getEquations()) {
      if (ec == _equ) ecbuilder.add(newequ);
      else ecbuilder.add(ec);
    }

    FixedList<EquationContext> newEquations = ecbuilder.build();
    FixedList<Hypothesis> newHypotheses = _state.getHypotheses().append(hypothesis);
    FixedList<OrdReq> newReqs = _state.getOrderingRequirements().append(_requirements);

    return new ProofState(newEquations, newHypotheses, newReqs, index);
  }

  @Override
  public String commandDescription() {
    return "induct";
  }

  @Override
  public void explain(OutputModule module) {
    if (_requirements.size() == 0) {
      module.println("We apply INDUCT to %a, which does not ipmose any new ordering requirements " +
        "but simply adds %a to the set H of induction hypotheses.", _equ,
        _equ.getEquation().makePrintableWith(_equ.getRenaming()));
    }
    else {
      module.print("We apply INDUCT to %a, which adds the equation into H, and imposes the " +
        "ordering requirement", _equ);
      if (_requirements.size() == 1) module.println(" %a.", _requirements.get(0));
      else module.println("s %a and %a.", _requirements.get(0), _requirements.get(1));
    }
  }
}

