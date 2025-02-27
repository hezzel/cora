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
import cora.rwinduction.engine.OrdReq;
import cora.rwinduction.engine.ProofState;
import cora.rwinduction.parser.CommandParsingStatus;

/** The environment command :ordering, which prints all the current ordering requirements. */
public class CommandOrdering extends Command {
  @Override
  public String queryName() {
    return ":ordering";
  }

  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of(":ordering");
  }

  @Override
  public String helpDescriptor() {
    return "List all the ordering requirements that have so far been imposed.";
  }

  @Override
  protected boolean run(CommandParsingStatus input) {
    if (!input.commandEnded()) {
      _module.println("Unexpected argument at position %a: :ordering does not take any " +
        "arguments.", input.currentPosition());
        return false;
    }
    ProofState state = _proof.getProofState();
    if (state.getOrderingRequirements().size() == 0) {
      _module.println("No ordering requirements have been imposed so far.");
    }
    else {
      _module.println("So far the following ordering requirements have been imposed:");
      _module.startTable();
      for (OrdReq req : state.getOrderingRequirements()) _module.println("%a", req);
      _module.endTable();
    }
    return true;
  }
}

