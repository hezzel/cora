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
import cora.io.OutputModule;
import cora.rwinduction.engine.deduction.DeductionContext;

/** The syntax for the deduction command APPLICATION. */
public class CommandApplication extends SingularDeductionCommandInherit {
  @Override
  public String queryName() {
    return "application";
  }
  
  @Override
  public void printHelp(OutputModule module) {
    module.println("Use this deduction rule to split an equation f s1 ... sn = f t1 ... tn | " +
      "constr into the n equations si = ti | constr, regardless of whether f is a function " +
      "symbol or variable.");
    module.println("(Using this command typically loses completeness of the proof state.  In " +
      "cases where completeness may be preserved, the semiconstructor command should be used " +
      "instead.)");
  }
  
  @Override
  protected DeductionContext createStep() {
    return DeductionContext.createStep(_proof, optionalModule(), false);
  }
}

