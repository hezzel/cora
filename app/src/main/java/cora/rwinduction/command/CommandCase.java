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
import java.util.Optional;

import charlie.util.FixedList;
import charlie.terms.Term;
import cora.io.OutputModule;
import cora.rwinduction.engine.deduction.DeductionCase;
import cora.rwinduction.parser.CommandParsingStatus;

/** The syntax for the deduction command case. */
public class CommandCase extends DeductionCommand {
  @Override
  public String queryName() {
    return "case";
  }
  
  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of("calc <constraint>",
                        "calc <integer expression>",
                        "calc <variable>");
  }
  
  @Override
  public void printHelp(OutputModule module) {
    module.println("Use this deduction rule to split the current equation into one or more " +
      "cases.");
    module.startTable();
    module.nextColumn("*");
    module.println("If you provide a constraint as argument, two new equations are created: one " +
      "where the constraint holds, and one where it doesn't.");
    module.nextColumn("*");
    module.println("If you provide an integer expression, three equations are created: one with " +
      "exp > 0, one with exp = 0 and one with exp < 0.");
    module.nextColumn("*");
    module.println("Finally, if you provide a variable of a non-theory base type, then an " +
      "equation is created for all constructors that might instantiate this variable.");
    module.endTable();
  }

  @Override
  protected DeductionCase createStep(CommandParsingStatus input) {
    if (_proof.getProofState().isFinalState()) {
      _module.println("There is no equation to do a case analysis on.");
      return null;
    }
    if (input.commandEnded()) {
      _module.println("Case should be invoked with at least one argument.");
      return null;
    }
    Term term = input.readTerm(_proof.getContext().getTRS(),
      _proof.getProofState().getTopEquation().getRenamingCopy(), _module);
    if (term == null) return null;
    if (!input.commandEnded()) {
      _module.println("Unexpected argument at position %a: expected end of command.",
        input.currentPosition());
      return null;
    }
    return DeductionCase.createStep(_proof, Optional.of(_module), term);
  }

  @Override
  public List<TabSuggestion> suggestNext(String args) {
    return List.of(new TabSuggestion(null, "constraint, integer expression or variable"));
  }
}

