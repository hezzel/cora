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

import java.util.Set;
import cora.io.OutputModule;
import cora.io.ParseableTermPrinter;

/**
 * A DeductionStep carries all the information to execute a specific deduction step on a fixed
 * equation.  These are used for storing, recovering, and explaining a proof history.
 *
 * Instances of DeductionStep are allowed to be a mutable objects, since they may be built
 * gradually; however, once completed, a DeductionStep is not meant to be changed.
 */
public abstract class DeductionStep {
  public class InapplicableStepException extends Exception {
    public InapplicableStepException(String cmd, String mess) {
      super("Could not apply deduction step \"" + cmd + "\": " + mess);
    }
  }

  /**
   * Call this to get the result of applying the deduction step on the given partial proof.  This
   * will not do any labour-intensive checks!
   * Rather, it assumes that all the prerequisites to apply the step are already satisfied.  If
   * there is a problem with the application even when all steps are ignored that can be (for
   * example, the step refers to a position in an equation that has no subterm at that position),
   * then an InapplicableStepException will be thrown instead.
   */
  public final ProofState apply(PartialProof proof) throws InapplicableStepException {
    try { return applyIgnoreExceptions(proof); }
    catch (RuntimeException e) {
      throw new InapplicableStepException(toString(), e.getMessage());
    }
  }

  /**
   * Inheriting classes should override this function to implement the apply function.  Any
   * RuntimeExceptions may be ignored, as they will be caught and converted into an
   * InapplicableStepException.
   */
  protected abstract ProofState applyIgnoreExceptions(PartialProof proof);

  /**
   * This function provides a command that the user can execute to lead to the current deduction
   * step being executed (after doing the appropriate checks).  It uses the given
   * ParseableTermPrinter to do so.
   */
  public abstract String commandDescription(ParseableTermPrinter termPrinter);

  /**
   * This function prints an explanation of the deduction step to the given output module.
   */
  public abstract void explain(OutputModule module);

  public final String toString() { return commandDescription(new ParseableTermPrinter(Set.of())); }
}

