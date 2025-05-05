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

import charlie.exceptions.CustomParserException;
import charlie.util.Pair;
import charlie.util.FixedList;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.Renaming;
import charlie.terms.TermFactory;
import cora.io.OutputModule;
import cora.rwinduction.engine.DeductionStep;
import cora.rwinduction.engine.VariableNamer;
import cora.rwinduction.engine.deduction.DeductionAlterDefinitions;
import cora.rwinduction.engine.deduction.DeductionAlterRename;
import cora.rwinduction.parser.CommandParsingStatus;

/** The syntax for the deduction command alter. */
public class CommandAlter extends Command {
  @Override
  public String queryName() {
    return "alter";
  }
  
  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of("alter add <var> = <term> , ..., <var> = <term>",
                        "alter rename <name> := <newname> , ... , <name> := <newname>");
  }
  
  @Override
  public String helpDescriptor() {
    return "Use this deduction rule to change an equation to an equivalent one.  For now, we " +
           "restrict the ways to do this in only specific ways that we know lead to an " +
           "equivalent constraint without needing to send higher-order constraints into the SMT " +
           "solver.  More interesting varieties of ALTER may be added in the future.  For " +
           "ALTER ADD, all variables that you introduce must be fresh, while the terms may use " +
           "only variables that already occur in the equation context, or that have been " +
           "introduced by definition to the left.";
  }

  @Override
  protected boolean run(CommandParsingStatus input) {
    String action = input.nextWord();
    DeductionStep step = null;
    if (input.commandEnded()) {
      _module.println("Alter should be invoked with at least two arguments.");
      return false;
    }
    if (action.equals("add")) {
      Optional<DeductionAlterDefinitions> ostep = createAddStep(input);
      if (!ostep.isEmpty()) step = ostep.get();
    }
    if (action.equals("rename")) {
      Optional<DeductionAlterRename> rstep = createRenameStep(input);
      if (!rstep.isEmpty()) step = rstep.get();
    }
    if (step == null) return false;
    return step.verifyAndExecute(_proof, Optional.of(_module));
  }
  
  /** Handle an alter add command */
  Optional<DeductionAlterDefinitions> createAddStep(CommandParsingStatus input) {
    ArrayList<Pair<Pair<Variable,String>,Term>> definitions =
      new ArrayList<Pair<Pair<Variable,String>,Term>>();
    Renaming renaming = _proof.getProofState().getTopEquation().getRenamingCopy();
    VariableNamer namer = _proof.getContext().getVariableNamer();
    Optional<OutputModule> om = Optional.of(_module);
    while (true) {
      String varname = readFreshName(input, renaming);
      if (varname == null) return Optional.empty();
      if (!input.expect("=", om)) return Optional.empty();
      Term term = input.readTerm(_proof.getContext().getTRS(), renaming, _module);
      if (term == null) return Optional.empty();
      VariableNamer.VariableInfo info = namer.getVariableInfo(varname);
      Variable x = TermFactory.createVar(info.basename(), term.queryType());
      if (!renaming.setName(x, varname)) {
        _module.println("Name %a is not legal for (fresh) variables.", x.queryName());
        return Optional.empty();
      }
      Pair<Variable,String> varinfo = new Pair<Variable,String>(x, varname);
      definitions.add(new Pair<Pair<Variable,String>,Term>(varinfo, term));
      if (input.commandEnded()) break;
      if (!input.expect(",", om)) return Optional.empty();
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
  Optional<DeductionAlterRename> createRenameStep(CommandParsingStatus input) {
    ArrayList<Pair<String,String>> names = new ArrayList<Pair<String,String>>();
    Optional<OutputModule> om = Optional.of(_module);
    while (true) {
      String origname = input.readIdentifier(om, "existing variable name");
      if (origname == null) return Optional.empty();
      if (!input.expect(":=", om)) return Optional.empty();
      String newname = input.readIdentifier(om, "fresh variable name");
      if (newname == null) return Optional.empty();
      names.add(new Pair<String,String>(origname, newname));
      if (input.commandEnded()) break;
      if (!input.expect(",", om)) return Optional.empty();
    }
    return DeductionAlterRename.createStep(_proof, om, names);
  }

  /** Tab suggestions for this command are either variables, =, or a term. */
  @Override
  public ArrayList<TabSuggestion> suggestNext(String args) {
    ArrayList<TabSuggestion> ret = new ArrayList<TabSuggestion>();
    CommandParsingStatus status = new CommandParsingStatus(args);
    if (status.commandEnded()) {
      ret.add(new TabSuggestion("add", "keyword"));
      ret.add(new TabSuggestion("rename", "keyword"));
      return ret;
    }
    String w = status.nextWord();
    if (w.equals("add")) addAddSuggestions(status, ret);
    else if (w.equals("rename")) addRenameSuggestions(status, ret);
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
        for (String x : _proof.getProofState().getTopEquation().getRenamingCopy().range()) {
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
}

