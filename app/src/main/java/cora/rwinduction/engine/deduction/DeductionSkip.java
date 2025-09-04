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
import charlie.util.FixedList;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

public final class DeductionSkip extends DeductionStep {
  private DeductionSkip(ProofState state, ProofContext context) {
    super(state, context);
  }
 
  public static DeductionSkip createStep(PartialProof proof, Optional<OutputModule> module) {
    if (proof.getProofState().getEquations().size() == 0) {
      module.ifPresent(o -> o.println(
        "The SKIP rule cannot be applied, since there are no equations."));
      return null;
    }
    return new DeductionSkip(proof.getProofState(), proof.getContext());
  }

  @Override
  public boolean verify(Optional<OutputModule> module) {
    if (_state.getEquations().size() == 1) {
      return println(module, "The SKIP rule cannot be applied, since there is only one equation.");
    }
    return true;
  }

  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    FixedList<EquationContext> oldeqs = _state.getEquations();
    FixedList.Builder<EquationContext> neweqs =
      new FixedList.Builder<EquationContext>(oldeqs.size());
    neweqs.add(oldeqs.get(oldeqs.size()-1));
    for (int i = 0; i < oldeqs.size()-1; i++) neweqs.add(oldeqs.get(i));
    return new ProofState(neweqs.build(), _state.getHypotheses(), _state.getOrderingRequirements(),
                          _state.getIncompleteEquations(), _state.getLastUsedIndex());
  }

  @Override
  public String commandDescription() {
    return "skip";
  }

  @Override
  public void explain(OutputModule module) {
    module.println("We apply SKIP, which does not change the existing equations, but does " +
      "allow us to focus on a different one.");
  }
}

