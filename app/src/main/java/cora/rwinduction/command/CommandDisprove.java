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

import cora.io.OutputModule;
import cora.rwinduction.engine.DeductionStep;
import cora.rwinduction.engine.deduction.DeductionDisproveSemi;

public class CommandDisprove extends SingularDeductionCommandInherit {
  @Override
  public String queryName() {
    return "disprove";
  }
  
  @Override
  public void printHelp(OutputModule module) {
    module.println("Use this deduction rule to derive the contradiction: the initial set of " +
      "equations contains one that is NOT an inductive theorem.");
  }

  @Override
  protected DeductionStep createStep() {
    return DeductionDisproveSemi.createStep(_proof, optionalModule());
  }
}

