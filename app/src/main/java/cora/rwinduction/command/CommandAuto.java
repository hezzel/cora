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

import java.util.ArrayList;
import cora.io.OutputModule;
import cora.rwinduction.engine.DeductionStep;
import cora.rwinduction.engine.automation.AutomaticProver;

/**
 * The "auto" command does as much automatically as possible on a single goal.
 */
public class CommandAuto extends SingularCommandInherit {
  @Override
  public String queryName() {
    return "auto";
  }
  
  @Override
  public void printHelp(OutputModule module) {
    module.println("The \"auto\" step uses simplification and calculation steps on both sides " +
      "of the equation until it is in normal form (or at least: we cannot find any further " +
      "reduction steps), then attempts to use delete, hdelete, eq-delete, constructor or " +
      "disprove steps to remove or further simplify the result.");
    module.println("For now, induct, case and hypothesis steps are NOT done, as there are " +
      "typically choices involved there.");
  }

  @Override
  protected boolean run() {
    ArrayList<DeductionStep> steps = AutomaticProver.handleBasics(_proof);
    if (steps.isEmpty()) return failure("There is nothing obvious to be done.");
    _module.startTable();
    for (DeductionStep step : steps) {
      _module.println("%a", step.commandDescription());
    }
    _module.endTable();
    return true;
  }
}

