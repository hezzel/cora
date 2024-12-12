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

package cora.rwinduction.interactive;

import cora.io.OutputModule;
import cora.rwinduction.engine.ProofState;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.engine.Command;

/**
 * An EnvironmentCommand is a command that is not meant to manipulate the PartialProof, but which
 * is used by the interactive prover to manipulate the user environment or request information.
 *
 * Inheriting classes should override exactly one of the run functions: either to use a
 * PartialProof, just the ProofState, or nothing at all beyond the OutputModule.
 */
public abstract class EnvironmentCommand implements Command {
  /**
   * This executes the Command, taking the PartialProof into account.
   * (However, it should not ALTER the partial proof, as only Deduction rules are supposed to do
   * this.)
   */
  public void run(PartialProof proof, OutputModule module) {
    run(proof.getProofState(), module);
  }

  /**
   * This executes the command, considering only the current proof state and the output module.
   */
  protected void run(ProofState state, OutputModule module) {
    run(module);
  }

  /**
   * Inheriting classes should override this method (and not the other two run functions) to
   * implement the command's execution if it does not depend on the current state of the proof.
   */
  protected void run(OutputModule module) { }
}

