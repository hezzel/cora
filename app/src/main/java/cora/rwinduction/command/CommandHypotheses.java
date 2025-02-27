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
import cora.rwinduction.engine.Hypothesis;
import cora.rwinduction.engine.ProofState;
import cora.rwinduction.parser.CommandParsingStatus;

/** The environment command :hypotheses, which prints all the current induction hypotheses. */
public class CommandHypotheses extends Command {
  @Override
  public String queryName() {
    return ":hypotheses";
  }

  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of(":hypotheses");
  }

  @Override
  public String helpDescriptor() {
    return "List all the currently available induction hypotheses.";
  }

  @Override
  protected boolean run(CommandParsingStatus input) {
    if (!input.commandEnded()) {
      _module.println("Unexpected argument at position %a: :hypotheses does not take any " +
        "arguments.", input.currentPosition());
        return false;
    }
    ProofState state = _proof.getProofState();
    if (state.getHypotheses().size() == 0) {
      _module.println("There are currently no induction hypotheses.");
    }
    else {
      _module.println("You currently have the following induction hypotheses available:");
      _module.startTable();
      for (Hypothesis hypo : state.getHypotheses()) _module.println("%a", hypo);
      _module.endTable();
    }
    return true;
  }
}

