/**************************************************************************************************
 Copyright 2024-2025 Cynthia Kop

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

import charlie.exceptions.CustomParserException;
import charlie.util.Pair;
import charlie.util.FixedList;
import charlie.terms.Renaming;
import charlie.terms.Substitution;
import cora.rwinduction.engine.EquationPosition;
import cora.rwinduction.engine.deduction.DeductionSimplify;
import cora.rwinduction.parser.CommandParsingStatus;

/** The syntax for the deduction command simplify. */
public class CommandSimplify extends ReductionCommandInherit {
  public CommandSimplify() {
    super("simplify", "<rule>");
  }

  @Override
  public String helpDescriptor() {
    return "Use this deduction rule to rewrite the current equation with one of the known rules, " +
           "which might apply to some subterm of the left- or right-hand side of the equation.  " +
           "Note that rule names can be found using :rules, and positions have the form " +
           "L.<position> or R.<position>.  To simplify with a calculation rule, use the calc " +
           "command instead.";
  }

  protected boolean run(CommandParsingStatus input) {
    Optional<DeductionSimplify> step = createStep(input);
    if (step.isEmpty()) return false;
    return step.get().verifyAndExecute(_proof, Optional.of(_module));
  }

  /** Main functionality of run, separated out for the sake of unit testing. */
  Optional<DeductionSimplify> createStep(CommandParsingStatus input) {
    // get ruleName (which is a valid rule)
    String ruleName = readRuleName(input);
    if (ruleName == null) return Optional.empty();

    // get EquationPosition and Substitution
    Renaming ruleRenaming = _proof.getContext().getRenaming(ruleName);
    Pair<EquationPosition,Substitution> pair = readCommandRemainder(ruleRenaming, input);
    if (pair == null) return Optional.empty();

    // create step
    return DeductionSimplify.createStep(_proof, Optional.of(_module), ruleName,
                                        pair.fst(), pair.snd());
  }

  /**
   * Helper function for run / createStep: this reads an identifier from the input, checks that
   * it's a valid rule, and if so, returns it.  If not, an error message is printed and null is
   * returned.
   */
  private String readRuleName(CommandParsingStatus input) {
    String txt = input.nextWord();
    if (txt != null && _proof.getContext().hasRule(txt)) return txt;
    if (txt == null) _module.println("Simplify should be invoked with at least 1 argument.");
    else _module.println("No such rule: " + txt);
    return null;
  }
}

