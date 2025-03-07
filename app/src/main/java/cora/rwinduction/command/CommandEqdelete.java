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

import java.util.Optional;

import charlie.util.FixedList;
import cora.rwinduction.engine.deduction.DeductionEqdelete;
import cora.rwinduction.parser.CommandParsingStatus;

/** The syntax for the deduction command eq-delete. */
public class CommandEqdelete extends Command {
  @Override
  public String queryName() {
    return "eq-delete";
  }
  
  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of("eq-delete");
  }
  
  @Override
  public String helpDescriptor() {
    return "Use this deduction rule to delete the current equation, if the left-hand side has " +
           "the form C[s1,...,sn], the right-hand side C[t1,...,tn], and the constraint implies " +
           "that each si = ti.";
  }
  
  @Override
  protected boolean run(CommandParsingStatus input) {
    if (!input.commandEnded()) return failure("Eq-delete should be invoked without arguments.");
    Optional<DeductionEqdelete> step = DeductionEqdelete.createStep(_proof, optionalModule());
    if (step.isEmpty()) return false;
    return step.get().verifyAndExecute(_proof, optionalModule());
  }
}

