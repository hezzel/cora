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

import java.util.List;

import charlie.util.FixedList;
import cora.rwinduction.engine.EquationContext;
import cora.rwinduction.engine.ProofState;
import cora.rwinduction.parser.CommandParsingStatus;

/**
 * The environment command :equations, which prints all the current equations, either with the
 * full context, or only as an equation.
 */
public class CommandEquations extends Command {
  @Override
  public String queryName() {
    return ":equations";
  }

  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of(":equations", ":equations full");
  }

  @Override
  public String helpDescriptor() {
    return "List all the currently open equations (goals that we still need to prove).  " +
           "If you want to see the full equation context, use the \"full\" argument.";
  }

  @Override
  public List<TabSuggestion> suggestNext(String args) {
    if (!args.equals("")) return List.of(endOfCommandSuggestion());
    return List.of(endOfCommandSuggestion(), new TabSuggestion("full", "keyword"));
  }

  @Override
  protected boolean run(CommandParsingStatus input) {
    // syntax: :equations
    if (input.commandEnded()) {
      printEquations(false);
      return true;
    }
    if (input.nextWord().equals("full")) {
      printEquations(true);
      return true;
    }
    _module.println("Unexpected argument at position %a: :equations takes either no " +
      "arguments, or only the argument \"full\".", input.previousPosition());
    return false;
  }

  private void printEquations(boolean full) {
    ProofState state = _proof.getProofState();
    _module.startTable();
    for (EquationContext ec : state.getEquations()) {
      if (full) _module.println("%a", ec);
      else {
        _module.nextColumn("%a:", ec.getName());
        _module.println("%a", ec.getEquation().makePrintableWith(ec.getRenaming()));
      }
    }
    _module.endTable();
  }
}

