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
import cora.rwinduction.engine.deduction.DeductionContext;

/** The syntax for the deduction command APPLICATION. */
public class CommandApplication extends SingularCommandInherit {
  @Override
  public String queryName() {
    return "application";
  }
  
  @Override
  public String helpDescriptor() {
    return "Use this deduction rule to split an equation f s1 ... sn = f t1 ... tn | constr into " +
           "the n equations si = ti | constr, regardless of whether f is a function symbol or " +
           "variable.  Note that doing this may well lose completeness.";
  }
  
  @Override
  protected boolean run() {
    Optional<DeductionContext> step = DeductionContext.createStep(_proof, optionalModule(), false);
    if (step.isEmpty()) return false;
    return step.get().verifyAndExecute(_proof, optionalModule());
  }
}

