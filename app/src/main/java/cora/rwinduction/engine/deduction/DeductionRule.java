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

package cora.rwinduction.engine.deduction;

import java.util.Optional;
import cora.io.OutputModule;
import cora.rwinduction.engine.ProofState;
import cora.rwinduction.engine.DeductionStep;
import cora.rwinduction.engine.PartialProof;

/**
 * A DeductionRule is a structure that can update the current proof state.
 * It may correspond either to a user-given or to an automatically generated command.
 */
abstract class DeductionRule {
  protected PartialProof _proof;
  protected Optional<OutputModule> _module;

  /**
   * Generates a deduction rule that will manipulate proof states in the given partial proof.
   * Any printing will be done to the given output module.
   */
  protected DeductionRule(PartialProof proof, OutputModule module) {
    _proof = proof;
    _module = Optional.of(module);
  }

  /**
   * Generates a deduction rule that will manipulate proof states in the given partial proof.
   * No printing will be done to the given output module.
   */
  protected DeductionRule(PartialProof proof) {
    _proof = proof;
    _module = Optional.empty();
  }

  /**
   * This applies the given deduction step and updates the proof state accordingly.  If the step
   * fails, then an appropriate error message is printed to the underlying output module instead.
   * The return value indicates whether we were successful.
   */
  protected boolean applyStep(DeductionStep step) {
    if (step == null) return false;
    try {
      ProofState newstate = step.apply(_proof);
      if (newstate == null) return false;
      _proof.addProofStep(newstate, step);
      return true;
    }
    catch (DeductionStep.InapplicableStepException e) {
      println("%a", e.getMessage());
      return false;
    }
  }

  /**
   * This executes a println to the underlying output module, provided one is set, and otherwise
   * does nothing.
   */
  protected void println(String str, Object ...objects) {
    _module.ifPresent( o -> o.println(str, objects) );
  }

  /*
   * For consistency, every deduction rule is expected to define methods:
   *   DeductionStep createStep(arg_1,...,arg_n) (does not need to be public)
   *   public boolean apply(arg_1,...,arg_n)
   *
   * The first method should use the arguments to build a deduction step and return it, without
   * doing any expensive checks on whether prerequisites apply.  Inexpensive checks may still be
   * done, including the necessary checks to build the deduction step; if any of these checks fail,
   * the method may print a failure message to the output module (if any) and return null.
   *
   * The second method should call createStep to create a deduction step, check all the necessary
   * prerequisites, and if everything is successful, apply the deduction step and return true.
   * If no deduction step can be created, or any of the prerequisites fails, then a message may be
   * printed to the output module and false is returned.  Hence, apply will typically have side
   * effects (if an output module is set):
   * - a return value of true indicates that the proof state was changed
   * - a return value of false indicates that something was printed to the underlying output module
   *
   * We do not include either function as an abstract method, because argument counts and types may
   * vary between different instances of DeductionRule.  It is also possible for instances of
   * DeductionRule to supply multiple instances of either method, with different arguments.
   */
}

