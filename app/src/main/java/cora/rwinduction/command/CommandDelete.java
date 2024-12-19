/**************************************************************************************************
 Copyright 2024 Cynthia Kop

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
import cora.rwinduction.engine.DeductionDelete;

/** The syntax for the deduction command delete. */
public class CommandDelete extends Command {
  private DeductionDelete _drule;

  public CommandDelete() {
    _drule = null;
  }

  public String queryName() {
    return "delete";
  }
  
  public FixedList<String> callDescriptor() {
    return FixedList.of("delete");
  }
  
  public String helpDescriptor() {
    return "Use this deduction rule to delete the current equation, if either the left- and " +
           "right-hand side are equal, or if the constraint is unsatisfiable.";
  }
  
  protected boolean run(String args) {
    if (!args.equals("")) return failure("delete should be invoked without arguments");
    if (_drule == null) _drule = new DeductionDelete(_proof, _module);
    return _drule.apply();
  }
}

