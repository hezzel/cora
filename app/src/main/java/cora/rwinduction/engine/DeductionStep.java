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

package cora.rwinduction.engine;

import java.util.Optional;
import cora.io.OutputModule;

/**
 * A DeductionStep carries all the information to execute a specific deduction step on a fixed
 * equation.  These are used to update the proof state, but also for storing, recovering, and
 * explaining a proof history.
 *
 * Instances of DeductionStep are expected to be immutable objects.  They do not have a public
 * constructor, so can only be created through a static createStep() method.
 */
public abstract class DeductionStep {
  protected final ProofState _state;        // the proof state on which this step is applied
  protected final EquationContext _equ;     // the top equation equation context in _state
  protected final ProofContext _pcontext;   // the proof context in which this step is applied

  /**
   * Inheriting classes should call this constructor to set up the proof state and proof
   * context on which the deduction step will be applied.  Note that the proof state must be
   * non-empty.
   */
  protected DeductionStep(ProofState state, ProofContext context) {
    _state = state;
    _pcontext = context;
    _equ = state.getTopEquation();
  }

  /**
   * Creating a step does basic checks, but avoids any labour-intensive verification such as calls
   * to the SMT solver or termination checker.  Hence, before executing a step it is essential to
   * verify that we may indeed do so by calling verify.  This returns true if the step is valid,
   * false if not; in the latter case, an appropriate error message will be printed to the
   * given output module (if any).
   */
  public abstract boolean verify(Optional<OutputModule> module);

  /**
   * This function applies the step to the given partial proof.  If any errors occur while applying
   * it (for example because the step was not set up correctly), an error message will be printed to
   * the underlying output module (if any) instead; in this case false is returned.
   *
   * Note: this will not do any labour-intensive correctness checks!  Rather, it assumes that all
   * the prerequisites to apply the step are already satisfied.  To ensure that this is the case,
   * create the step using createStep(), and then call verify before calling execute.
   *
   * If there is a problem with the application even when all checks are ignored that can be (for
   * example, the step refers to a position in an equation that has no subterm at that position),
   * then an appropriate error message is printed to the given output module (if any), and false
   * is returned.  Otherwise, true is returned.
   */
  public final boolean execute(PartialProof proof, Optional<OutputModule> o) {
    if (proof.isDone()) return println(o, "The proof is already finished.");
    if (proof.getProofState() != _state) return println(o, "Cannot apply step to different state.");

    try {
      ProofState newstate = tryApply(o);
      if (newstate == null) return false; // in this case an error message was already given
      proof.addProofStep(newstate, this);
      return true;
    }
    catch (RuntimeException e) {
      println(o, "Error applying step: %a", e.getMessage());
      return false;
    }
  }

  /**
   * This function verifies the step, and if successful, executes it.
   * If either the verification or the application is unsuccessful, false is returned.
   */
  public final boolean verifyAndExecute(PartialProof proof, Optional<OutputModule> o) {
    return verify(o) && execute(proof, o);
  }

  /**
   * Inheriting classes should override this function to implement the execute function: it
   * should determine a new proof state (based on _state, _pcontext, and the nature of this
   * particular step), or return null.
   *
   * This function does not need to try catching any errors, as this will be handled by execute().
   */
  protected abstract ProofState tryApply(Optional<OutputModule> module);

  /**
   * Helper function for inheriting classes.
   * This executes a println to the underlying output module, provided one is set, and otherwise
   * does nothing.  It always returns false, to accommodate convenient printing before failure.
   */
  protected final boolean println(Optional<OutputModule> module, String str, Object ...objects) {
    module.ifPresent( o -> o.println(str, objects) );
    return false;
  }

  /** This returns the proof state that this command was applied on. */
  public final ProofState getOriginalState() {
    return _state;
  }

  /**
   * This function provides a command that the user can execute to lead to the current deduction
   * step being executed (after doing the appropriate checks).
   */
  public abstract String commandDescription();

  /**
   * This function prints an explanation of the deduction step to the given output module.
   */
  public abstract void explain(OutputModule module);

  /** Returns the commandDescription as a representation of the step. */
  public final String toString() {
    return commandDescription();
  }

  /**
   * Helper function for the static createStep function: this returns either the top equation
   * in the given proof state, or null if the proof state is already final.  If the module is set,
   * then an appropriate error message will be printed in the latter case.
   */
  public static Equation getTopEquation(ProofState state, Optional<OutputModule> module) {
    if (state.isFinalState()) {
      module.ifPresent( o -> o.println("The proof is already complete.") );
      return null;
    }
    return state.getTopEquation().getEquation();
  }
}

