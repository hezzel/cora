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
import charlie.theory.Theory;
import cora.io.OutputModule;
import cora.rwinduction.engine.DeductionStep;
import cora.rwinduction.engine.VariableNamer;
import cora.rwinduction.engine.deduction.DeductionAlterConstraint;
import cora.rwinduction.engine.deduction.DeductionAlterDefinitions;
import cora.rwinduction.engine.deduction.DeductionAlterObserve;
import cora.rwinduction.engine.deduction.DeductionAlterRename;
import cora.rwinduction.parser.CommandParsingStatus;

/** The syntax for the deduction command alter. */
public class CommandAlter extends DeductionCommand {
  @Override
  public String queryName() {
    return "alter";
  }
  
  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of("alter add <var> = <term> , ..., <var> = <term>",
                        "alter rename <name> := <newname> , ... , <name> := <newname>",
                        "alter observe <var> = <term>",
                        "alter constraint <constraint>");
  }
  
  @Override
  public void printHelp(OutputModule module) {
    module.println("Use this deduction rule to change an equation to an equivalent one.  " +
      "For now, we restrict the ways to do this in only specific ways that we know lead to an " +
      "equivalent constraint without needing to send higher-order constraints into the SMT " +
      "solver.  More interesting varieties of ALTER may be added in the future.");
    module.println("For ALTER ADD, all variables that you introduce must be fresh, while the " +
      "terms may use only variables that already occur in the equation context, or that have " +
      "been introduced by definition to the left.");
    module.println("For ALTER RENAME, note that the new names you introduce should not occur " +
      "in the bounding terms either!");
    module.println("For ALTER OBSERVE, the term should be a variable or value which, according " +
      "to the constraint, is equal to the given variable.");
    module.println("For ALTER CONSTRAINT, the new constraint should be equivalent to the " +
      "original one. No fresh variables are allowed to occur in it (but you can add variables " +
      "that occur only in the body of the equation context, not yet the constraint).");
  }

  @Override
  protected DeductionStep createStep(CommandParsingStatus input) {
    String action = input.nextWord();
    if (input.commandEnded()) {
      _module.println("Alter should be invoked with at least two arguments.");
      return null;
    }
    if (action.equals("add")) return createAddStep(input);
    if (action.equals("rename")) return createRenameStep(input);
    if (action.equals("observe")) return createObserveStep(input);
    if (action.equals("constraint")) return createConstraintStep(input);
    _module.println("Unknown action for alter: %a.", action);
    return null;
  }
  
  /** Creates the deduction step for an alter add command */
  DeductionAlterDefinitions createAddStep(CommandParsingStatus input) {
    ArrayList<Pair<Pair<Variable,String>,Term>> definitions =
      new ArrayList<Pair<Pair<Variable,String>,Term>>();
    MutableRenaming renaming = _proof.getProofState().getTopEquation().getRenaming().copy();
    VariableNamer namer = _proof.getContext().getVariableNamer();
    Optional<OutputModule> om = optionalModule();
    while (true) {
      String varname = readFreshName(input, renaming);
      if (varname == null) return null;
      if (!input.expect("=", om)) return null;
      Term term = input.readTerm(_proof.getContext().getTRS(), renaming, _module);
      if (term == null) return null;
      VariableNamer.VariableInfo info = namer.getVariableInfo(varname);
      Variable x = TermFactory.createVar(info.basename(), term.queryType());
      if (!renaming.setName(x, varname)) {
        _module.println("Name %a is not legal for (fresh) variables.", x.queryName());
        return null;
      }
      Pair<Variable,String> varinfo = new Pair<Variable,String>(x, varname);
      definitions.add(new Pair<Pair<Variable,String>,Term>(varinfo, term));
      if (input.commandEnded()) break;
      if (!input.expect(",", om)) return null;
    }

    return DeductionAlterDefinitions.createStep(_proof, om, definitions);
  }

  /**
   * Helper function for createAddStep: this reads a single identifier, which should be the name
   * for a fresh variable.
   */
  private String readFreshName(CommandParsingStatus input, Renaming renaming) {
    int p = input.currentPosition();
    String varname = input.readIdentifier(Optional.of(_module), "fresh variable name");
    if (varname == null) return null;
    if (renaming.getReplaceable(varname) != null) {
      _module.println("Variable %a at position %a is already known in this equation " +
        "context.  Please choose a fresh name.", varname, input.previousPosition());
      return null;
    }
    return varname;
  }

  /** Handle an alter rename command */
  DeductionAlterRename createRenameStep(CommandParsingStatus input) {
    ArrayList<Pair<String,String>> names = new ArrayList<Pair<String,String>>();
    Optional<OutputModule> om = optionalModule();
    while (true) {
      String origname = input.readIdentifier(om, "existing variable name");
      if (origname == null) return null;
      if (!input.expect(":=", om)) return null;
      String newname = input.readIdentifier(om, "fresh variable name");
      if (newname == null) return null;
      names.add(new Pair<String,String>(origname, newname));
      if (input.commandEnded()) break;
      if (!input.expect(",", om)) return null;
    }
    return DeductionAlterRename.createStep(_proof, om, names);
  }

  /** Handle an alter observe command */
  DeductionAlterObserve createObserveStep(CommandParsingStatus input) {
    Optional<OutputModule> om = optionalModule();
    Renaming renaming = _proof.getProofState().getTopEquation().getRenaming();
    String originalname = input.readIdentifier(om, "existing variable name");
    if (originalname == null) return null;
    Variable original = null;
    if (renaming.getReplaceable(originalname) != null &&
        renaming.getReplaceable(originalname) instanceof Variable o) original = o;
    else {
      _module.println("No such variable: %a.", originalname);
      return null;
    }
    if (!input.expect("=", om)) return null;
    Term replacement = input.readTerm(_proof.getContext().getTRS(), renaming, _module);
    if (replacement == null) return null;
    return DeductionAlterObserve.createStep(_proof, om, original, replacement);
  }

  /** Handle an alter constraint command */
  DeductionAlterConstraint createConstraintStep(CommandParsingStatus input) {
    Term constraint = input.readTerm(_proof.getContext().getTRS(),
                                     _proof.getProofState().getTopEquation().getRenaming(),
                                     _module);
    if (constraint == null) return null;
    return DeductionAlterConstraint.createStep(_proof, optionalModule(), constraint);
  }

  @Override
  public ArrayList<TabSuggestion> suggestNext(String args) {
    ArrayList<TabSuggestion> ret = new ArrayList<TabSuggestion>();
    CommandParsingStatus status = new CommandParsingStatus(args);
    if (status.commandEnded()) {
      ret.add(new TabSuggestion("add", "keyword"));
      ret.add(new TabSuggestion("rename", "keyword"));
      ret.add(new TabSuggestion("observe", "keyword"));
      ret.add(new TabSuggestion("constraint", "keyword"));
      return ret;
    }
    String w = status.nextWord();
    if (w.equals("add")) addAddSuggestions(status, ret);
    else if (w.equals("rename")) addRenameSuggestions(status, ret);
    else if (w.equals("observe")) addObserveSuggestions(status, ret);
    else if (w.equals("constraint")) addConstraintSuggestions(status, ret);
    return ret;
  }

  /** Tab suggestions once "alter add" has been read. */
  private void addAddSuggestions(CommandParsingStatus status, ArrayList<TabSuggestion> ret) {
    int kind = 1;
    Optional<OutputModule> empty = Optional.empty();
    while (kind > 0 && !status.commandEnded()) {
      if (kind == 1) {
        String name = status.readIdentifier(empty, "identifier");
        if (name == null || name.equals("")) kind = -1;
        else kind = 2;
      }
      else if (kind == 2) {
        if (status.expect("=", empty)) kind = 3;
        else kind = -1;
      }
      else if (kind == 3) {
        if (status.skipTerm()) kind = 4;
        else break;
      }
      else {
        if (status.expect(",", empty)) kind = 1;
        else { status.nextWord(); kind = -1; }
      }
    }
    if (kind == 1) ret.add(new TabSuggestion(null, "variable name"));
    if (kind == 2) ret.add(new TabSuggestion("=", "keyword"));
    if (kind == 3) ret.add(new TabSuggestion(null, "term"));
    if (kind == 4) {
      ret.add(new TabSuggestion(null, "rest of term"));
      ret.add(new TabSuggestion(",", "keyword"));
      ret.add(endOfCommandSuggestion());
    }
  }

  /** Tab suggestions once "alter rename" has been read. */
  private void addRenameSuggestions(CommandParsingStatus status, ArrayList<TabSuggestion> ret) {
    int kind = 1;
    Optional<OutputModule> empty = Optional.empty();
    while (kind > 0 && !status.commandEnded()) {
      if (kind == 1 || kind == 3) {
        String name = status.readIdentifier(empty, "identifier");
        if (name == null || name.equals("")) kind = -1;
        else kind++;
      }
      else if (kind == 2) {
        if (status.expect(":=", empty)) kind = 3;
        else kind = -1;
      }
      else {
        if (status.expect(",", empty)) kind = 1;
        else { status.nextWord(); kind = -1; }
      }
    }
    if (kind == 1) {
      if (_proof.getProofState().getEquations().isEmpty()) {
        ret.add(new TabSuggestion(null, "existing variable name"));
      }
      else {
        for (String x : _proof.getProofState().getTopEquation().getRenaming().range()) {
          ret.add(new TabSuggestion(x, "existing variable name"));
        }
      }
    }
    if (kind == 2) ret.add(new TabSuggestion(":=", "keyword"));
    if (kind == 3) ret.add(new TabSuggestion(null, "fresh variable name"));
    if (kind == 4) {
      ret.add(new TabSuggestion(",", "keyword"));
      ret.add(endOfCommandSuggestion());
    }
  }

  /** Tab suggestions once "alter observe" has been read. */
  private void addObserveSuggestions(CommandParsingStatus status, ArrayList<TabSuggestion> ret) {
    Optional<OutputModule> empty = Optional.empty();
    if (status.commandEnded()) {
      addVariableSuggestions(ret);
      return;
    }
    String originalname = status.readIdentifier(empty, "existing variable name");
    if (status.commandEnded()) {
      ret.add(new TabSuggestion("=", "keyword"));
      return;
    }
    if (!status.expect("=", empty)) return;
    if (status.commandEnded()) {
      addVariableReplacementSuggestions(originalname, ret);
      ret.add(new TabSuggestion(null, "value"));
      return;
    }
    ret.add(endOfCommandSuggestion());
  }

  /**
   * Helper function for alter observe: this adds possible variables to ret that occur in left-
   * or right-hand side of the current equation, and which have a theory sort for a type.
   */
  private void addVariableSuggestions(ArrayList<TabSuggestion> ret) {
    Renaming renaming = _proof.getProofState().getTopEquation().getRenaming();
    Term left = _proof.getProofState().getTopEquation().getLhs();
    Term right = _proof.getProofState().getTopEquation().getRhs();
    for (String name : renaming.range()) {
      var x = renaming.getReplaceable(name);
      if (left.queryFreeReplaceables().contains(x) || right.queryFreeReplaceables().contains(x)) {
        if (Theory.isTheory(x.queryType()) && x.queryType().isBaseType()) {
          ret.add(new TabSuggestion(name, "existing theory variable"));
        }
      }
    }
  }

  /**
   * Helper function for alter observe: this adds possible variable suggestions of the same type as
   * the given variable, if any exist (other than varname itself).
   */
  private void addVariableReplacementSuggestions(String varname, ArrayList<TabSuggestion> ret) {
    Renaming renaming = _proof.getProofState().getTopEquation().getRenaming();
    var x = renaming.getReplaceable(varname);
    if (x == null) return;
    for (String name : renaming.range()) {
      if (name.equals(varname)) continue;
      if (renaming.getReplaceable(name).queryType().equals(x.queryType())) {
        ret.add(new TabSuggestion(name, "variable"));
      }
    }
  }

  /** Tab suggestions once "alter constraint" has been read. */
  private void addConstraintSuggestions(CommandParsingStatus status, ArrayList<TabSuggestion> ret) {
    if (status.commandEnded()) ret.add(new TabSuggestion(null, "constraint"));
    else {
      ret.add(new TabSuggestion(null, "rest of constraint"));
      ret.add(endOfCommandSuggestion());
    }
  }
}

