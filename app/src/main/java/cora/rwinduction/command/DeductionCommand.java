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

package cora.rwinduction.command;

import java.util.List;
import java.util.Optional;

import charlie.util.FixedList;
import cora.io.OutputModule;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.engine.DeductionStep;
import cora.rwinduction.parser.CommandParsingStatus;

/**
 * A DeductionCommand is a Command that creates a deduction step, and then executes it.
 * Since executing deduction steps can be complex, there is also an option to do so without the
 * expensive checks, which is useful when restoring work we have previously confirmed is correct.
 */
public abstract class DeductionCommand extends Command {
  protected DeductionCommand(PartialProof pp, OutputModule om) {
    super(pp, om);
  }

  protected DeductionCommand() {
    super();
  }

  protected final boolean run(CommandParsingStatus input) {
    DeductionStep step = createStep(input);
    if (step == null) return false;
    return step.verifyAndExecute(_proof, optionalModule());
  }

  public final boolean executeWithoutVerification(CommandParsingStatus input) {
    DeductionStep step = createStep(input);
    if (step == null) return false;
    return step.execute(_proof, optionalModule());
  }

  /**
   * If successful, this returns a DeductionStep representing the command as given by input.
   * If not, this will return null.
   */
  protected abstract DeductionStep createStep(CommandParsingStatus input);
}

