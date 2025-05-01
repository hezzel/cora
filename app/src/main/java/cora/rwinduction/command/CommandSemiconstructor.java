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
import cora.rwinduction.engine.deduction.DeductionConstructor;

/** The syntax for the deduction command SEMICONSTRUCTOR. */
public class CommandSemiconstructor extends SingularCommandInherit {
  @Override
  public String queryName() {
    return "semiconstructor";
  }
  
  @Override
  public String helpDescriptor() {
    return "Use this deduction rule to split an equation f s1 ... sn = f t1 ... tn | constr into " +
           "the n equations si = ti | constr, if f is a constructor, or its arity is greater " +
           "than n.";
  }
  
  @Override
  protected boolean run() {
    Optional<DeductionConstructor> step = DeductionConstructor.createStep(_proof, optionalModule());
    if (step.isEmpty()) return false;
    return step.get().verifyAndExecute(_proof, optionalModule());
  }
}

