/**************************************************************************************************
 Copyright 2024-2025 Cynthia Kop

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
import cora.io.OutputModule;
import cora.rwinduction.engine.deduction.DeductionDelete;

/** The syntax for the deduction command delete. */
public class CommandDelete extends SingularDeductionCommandInherit {
  @Override
  public String queryName() {
    return "delete";
  }
  
  @Override
  public void printHelp(OutputModule module) {
    module.println("Use this deduction rule to delete the current equation, if either the left- " +
      "and right-hand side are equal, or if the constraint is unsatisfiable.");
  }
  
  @Override
  protected DeductionDelete createStep() {
    return DeductionDelete.createStep(_proof, optionalModule());
  }
}

