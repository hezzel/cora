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

import java.util.ArrayList;
import java.util.Optional;

import charlie.util.Pair;
import charlie.util.FixedList;
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.TermFactory;
import cora.io.OutputModule;
import cora.rwinduction.engine.DeductionStep;
import cora.rwinduction.engine.VariableNamer;
import cora.rwinduction.engine.deduction.DeductionAlterGeneraliseConstraint;
import cora.rwinduction.engine.deduction.DeductionGeneraliseDrop;
import cora.rwinduction.engine.deduction.DeductionGeneraliseSubterm;
import cora.rwinduction.parser.CommandParsingStatus;

/** The syntax for the deduction command generalise. */
public class CommandGeneralise extends DeductionCommand {
  @Override
  public String queryName() {
    return "generalise";
  }
  
  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of("generalise subterm <term> as <variable>",
                        "generalise drop <constraint>",
                        "generalise constraint <constraint>");
  }
  
  @Override
  public void printHelp(OutputModule module) {
    module.println("Use this deduction rule to replace an equation by a more general one.  " +
      "This causes completeness to be lost.  Currently, there are three supported ways of " +
      "generalising:");
    module.startTable();
    module.nextColumn("*");
    module.println("Replacing all instances of a specific subterm by a variable.  If the current " +
      "bounding terms are not the top element, then most likely, they will be tightened to the " +
      "corresponding side of the equation.");
    module.nextColumn("*");
    module.println("Dropping a part of the constraint.  If the constraint currently has a form " +
      "part1 %{and} ... %{and} partn, you can supply parti or some conjunction of parti elements " +
      "which are then removed from the constraint.  This does not cause the bounding terms to be " +
      "changed, and does not require an invocation of the SMT-solver.");
    module.nextColumn("*");
    module.println("Generalising the constraint to an implied one.  This does require an " +
      "invocation of the SMT-solver to ensure that the new constraint you supply is indeed " +
      "implied.  Note that the new constraint may not have any variables that do not occur in " +
      "the original one.");
    module.endTable();
  }

  @Override
  protected DeductionStep createStep(CommandParsingStatus input) {
    String action = input.nextWord();
    if (input.commandEnded()) {
      _module.println("Generalise should be invoked with at least two arguments.");
      return null;
    }
    Renaming renaming = _proof.getProofState().getTopEquation().getRenaming();
    Term term = input.readTerm(_proof.getContext().getTRS(), renaming, _module);
    if (term == null) return null;
    if (action.equals("subterm")) return createSubtermStep(input, term);
    if (action.equals("drop")) return createDropStep(input, term);
    if (action.equals("constraint")) return createConstraintStep(input, term);
    _module.println("Unknown action for alter: %a.", action);
    return null;
  }
  
  /** Creates the deduction step for a generalise subterm command */
  DeductionGeneraliseSubterm createSubtermStep(CommandParsingStatus input, Term subterm) {
    Optional<OutputModule> om = Optional.of(_module);
    if (!input.expect("as", om)) return null;
    String name = input.nextWord();
    if (name == null) {
      _module.println("Missing variable name at position %a.", input.currentPosition());
      return null;
    }
    if (!input.commandEnded()) {
      _module.println("Unexpected argument at position %a: generalise subterm command should " +
        "end after the variable name.", input.currentPosition());
      return null;
    }
    return DeductionGeneraliseSubterm.createStep(_proof, om, subterm, name);
  }

  /** Creates the deduction step for a generalise drop command */
  DeductionGeneraliseDrop createDropStep(CommandParsingStatus input, Term drop) {
    if (!input.commandEnded()) {
      _module.println("Unexpected argument at position %a: expected end of command.",
        input.currentPosition());
      return null;
    }
    return DeductionGeneraliseDrop.createStep(_proof, Optional.of(_module), drop);
  }

  /** Creates the deduction step for a generalise constraint command */
  DeductionAlterGeneraliseConstraint createConstraintStep(CommandParsingStatus input, Term c) {
    if (!input.commandEnded()) {
      _module.println("Unexpected argument at position %a: expected end of command.",
        input.currentPosition());
      return null;
    }
    return DeductionAlterGeneraliseConstraint.createGeneraliseStep(_proof, Optional.of(_module), c);
  }


  @Override
  public ArrayList<TabSuggestion> suggestNext(String args) {
    ArrayList<TabSuggestion> ret = new ArrayList<TabSuggestion>();
    CommandParsingStatus status = new CommandParsingStatus(args);
    if (status.commandEnded()) {
      ret.add(new TabSuggestion("subterm", "keyword"));
      ret.add(new TabSuggestion("drop", "keyword"));
      ret.add(new TabSuggestion("constraint", "keyword"));
      return ret;
    }
    String w = status.nextWord();
    if (w.equals("subterm")) addSubtermSuggestions(status, ret);
    else addConstraintSuggestions(status, ret);
    return ret;
  }

  /** Tab suggestions once "generalise subterm" has been read. */
  private void addSubtermSuggestions(CommandParsingStatus status, ArrayList<TabSuggestion> ret) {
    if (status.commandEnded() || !status.skipTerm()) ret.add(new TabSuggestion(null, "term"));
    else if (status.commandEnded()) ret.add(new TabSuggestion("as", "keyword"));
    else if (status.nextWord().equals("as") && status.commandEnded()) {
      ret.add(new TabSuggestion(null, "variable name"));
    }
    else ret.add(endOfCommandSuggestion());
  }

  /** Tab suggestions for only reading a constraint */
  private void addConstraintSuggestions(CommandParsingStatus status, ArrayList<TabSuggestion> ret) {
    if (status.commandEnded()) ret.add(new TabSuggestion(null, "constraint"));
    else {
      ret.add(new TabSuggestion(null, "rest of constraint"));
      if (status.skipTerm() && status.commandEnded()) ret.add(endOfCommandSuggestion());
    }
  }
}

