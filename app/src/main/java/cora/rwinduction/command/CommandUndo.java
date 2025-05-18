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
import charlie.util.FixedList;
import cora.io.OutputModule;
import cora.rwinduction.parser.CommandParsingStatus;

/** The syntax for the undo command. */
public class CommandUndo extends SingularCommandInherit {
  @Override
  public String queryName() {
    return "undo";
  }
  
  @Override
  public void printHelp(OutputModule module) {
    module.println("Use this deduction rule to undo the last deduction step.  If you go too far, " +
      "you can still use \"redo\" to get back to the current state.");
  }

  @Override
  protected boolean run() {
    if (!_proof.undoProofStep()) return failure("Nothing to undo.");
    return true;
  }
}

