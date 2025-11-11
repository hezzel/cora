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

import charlie.util.Pair;
import charlie.terms.replaceable.Renaming;
import charlie.substitution.Substitution;
import cora.io.OutputModule;
import cora.rwinduction.engine.EquationPosition;
import cora.rwinduction.engine.Hypothesis;
import cora.rwinduction.engine.DeductionStep;
import cora.rwinduction.engine.deduction.DeductionHdelete;
import cora.rwinduction.engine.automation.AutoDeleter;
import cora.rwinduction.parser.CommandParsingStatus;

/** The syntax for the deduction command hdelete. */
public class CommandHdelete extends HypothesisCommandInherit {
  public CommandHdelete() {
    super("hdelete");
  }

  @Override
  public void printHelp(OutputModule module) {
    module.println("Use this deduction rule to rewrite one side of the current equation to the " +
      "other side, using one of the current induction hypotheses in the proof state.");
    module.println("Note that induction hypotheses can be found using :hypotheses, and that " +
      "positions have the form L.%{langle}position%{rangle} or R.%{langle}position%{rangle}.");
    module.println("To use the inverse of an induction hypothesis, use for instance H5^{-1} or " +
      "H5-inverse.  (Or just apply the deduction rule on the other side!)");
  }

  @Override
  protected DeductionStep createStep(CommandParsingStatus input) {
    // handle no-arguments case
    if (input.commandEnded()) return AutoDeleter.createHdeleteStep(_proof, Optional.of(_module));
    // get induction hypothesis and inverse status
    Pair<Hypothesis,Boolean> hypopair = readHypothesis(input);
    if (hypopair == null) return null;
    // get EquationPosition and Substitution
    Renaming hypoRenaming = hypopair.fst().getRenaming();
    Pair<EquationPosition,Substitution> restpair = readCommandRemainder(hypoRenaming, input);
    if (restpair == null) return null;
    return DeductionHdelete.createStep(_proof, Optional.of(_module), hypopair.fst(),
                                       hypopair.snd(), restpair.fst(), restpair.snd());
  }
}

