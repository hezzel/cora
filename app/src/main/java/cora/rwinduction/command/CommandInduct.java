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
import cora.io.OutputModule;
import cora.rwinduction.engine.deduction.DeductionInduct;
import cora.rwinduction.parser.CommandParsingStatus;

public class CommandInduct extends SingularCommandInherit {
  @Override
  public String queryName() {
    return "induct";
  }
  
  @Override
  public void printHelp(OutputModule module) {
    module.println("Use this deduction rule to store the current equation as an induction " +
      "hypothesis..");
  }

  @Override
  protected boolean run() {
    Optional<OutputModule> o = Optional.of(_module);
    Optional<DeductionInduct> step = DeductionInduct.createStep(_proof, o);
    if (step.isEmpty()) return false;
    return step.get().verifyAndExecute(_proof, o);
  }
}

