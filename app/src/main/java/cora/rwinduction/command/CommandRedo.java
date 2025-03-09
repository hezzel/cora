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

import charlie.util.FixedList;
import cora.rwinduction.parser.CommandParsingStatus;

/** The syntax for the redo command. */
public class CommandRedo extends SingularCommandInherit {
  @Override
  public String queryName() {
    return "redo";
  }
  
  @Override
  public String helpDescriptor() {
    return "If you have just applied the undo command, you can use this rule to get back to the " +
           "previous proof state (before undoing).  Note that doing any step other than undo or " +
           "redo will cause the \"future\" states to be forgotten, at which point you cannot " +
           "redo these steps anymore.";
  }

  @Override
  protected boolean run() {
    if (!_proof.redoProofStep()) return failure("Nothing to redo.");
    return true;
  }
}

