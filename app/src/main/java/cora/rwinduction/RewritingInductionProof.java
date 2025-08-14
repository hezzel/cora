/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rwinduction;

import java.util.ArrayList;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.rwinduction.engine.*;

public class RewritingInductionProof implements ProofObject {
  private ArrayList<DeductionStep> _steps;
  private ProofState _finalState;
  private ProofObject _terminationProof;

  public RewritingInductionProof(PartialProof proof) {
    _finalState = proof.getProofState();
    _steps = proof.getDeductionHistory();
    _terminationProof = proof.getTerminationProof();
  }

  public Answer queryAnswer() {
    if (_finalState.isFinalState() && _terminationProof != null) return Answer.YES;
    return Answer.MAYBE;
  }

  public void justify(OutputModule module) {
    ProofState start = _steps.size() == 0 ? _finalState : _steps.get(0).getOriginalState();
    module.println("We start the process with the following equations:");
    printEquations(module, start.getEquations());
    for (int i = 0; i < _steps.size(); i++) {
      _steps.get(i).explain(module);
      ProofState curr = _steps.get(i).getOriginalState();
      ProofState next = i + 1 < _steps.size() ? _steps.get(i+1).getOriginalState()
                                              : _finalState;
      ArrayList<EquationContext> neweqs = getNewEquations(next, curr.getLastUsedIndex());
      if (neweqs.size() == 1) module.println("This yields %a", neweqs.get(0));
      else if (neweqs.size() > 0) {
        module.println("This yields the following new equations:");
        printEquations(module, neweqs);
      }
    }
    if (_finalState.isFinalState()) {
      if (_terminationProof == null || _terminationProof.queryAnswer() != ProofObject.Answer.YES) {
        module.println("All equations have been removed, so the proof is complete: the original " +
          "equations are inductive theorems, provided the underlying ordering requirements can " +
          "be satisfied.  Unfortunately, the existence of a suitable ordering has not yet been " +
          "proved.");
      }
      else {
        module.println("All equations have been removed, so the proof is complete: the original " +
          "equations are inductive theorems.  The existence of a suitable bounding pair is " +
          "guaranteed by the termination of the corresponding term rewriting systems, as " +
          "is demonstrated below.");
        _terminationProof.justify(module);
      }
    }
    else {
      module.println("The proof attempt was aborted before a proof could be found.");
    }

    module.println("Steps:");
    module.startTable();
    for (int i = 0; i < _steps.size(); i++) {
      module.println("%a", _steps.get(i).commandDescription());
    }
    module.endTable();
  }
  
  /**
   * Helper function for justify: returns all equations in the given proof state whose index is
   * greater than [morethan].
   */
  private ArrayList<EquationContext> getNewEquations(ProofState state, int morethan) {
    ArrayList<EquationContext> ret = new ArrayList<EquationContext>();
    for (EquationContext eq : state.getEquations()) {
      if (eq.getIndex() > morethan) ret.add(eq);
    }
    return ret;
  }

  /** Helper function for explain: prints the equations given by the given iterable. */
  private void printEquations(OutputModule module, Iterable<EquationContext> eqs) {
    module.startTable();
    for (EquationContext eq : eqs) module.println("%a", eq);
    module.endTable();
  }
}

