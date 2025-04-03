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
import cora.rwinduction.engine.DeductionStep;
import cora.rwinduction.engine.VariableNamer;
import cora.rwinduction.engine.deduction.DeductionAlterDefinitions;
import cora.rwinduction.parser.CommandParsingStatus;

/** The syntax for the deduction command alter. */
public class CommandAlter extends Command {
  @Override
  public String queryName() {
    return "alter";
  }
  
  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of("alter add <var> = <term> , ..., <var> = <term>");
  }
  
  @Override
  public String helpDescriptor() {
    return "Use this deduction rule to change an equation to an equivalent one.  For now, we " +
           "restrict the ways to do this in only specific ways that we know lead to an " +
           "equivalent constraint without needing to send higher-order constraints into the SMT " +
           "solver.  More interesting varieties of ALTER may be added in the future.  For " +
           "ALTER ADD, all variables that you introduce must be fresh, while the terms may use " +
           "only variables that already occur in the equation context, or that have been " +
           "introduced by definition to the left. Note that spaces are required in this syntax.";
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
    if (step == null) return false;
    return step.verifyAndExecute(_proof, Optional.of(_module));
  }
  
  /** Handle an alter add command */
  Optional<DeductionAlterDefinitions> createAddStep(CommandParsingStatus input) {
    ArrayList<Pair<Pair<Variable,String>,Term>> definitions =
      new ArrayList<Pair<Pair<Variable,String>,Term>>();
    Renaming renaming = _proof.getProofState().getTopEquation().getRenamingCopy();
    VariableNamer namer = _proof.getContext().getVariableNamer();
    while (true) {
      String varname = readFreshName(input, renaming);
      if (varname == null) return Optional.empty();
      if (!expect(input, "=")) return Optional.empty();
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
      if (!expect(input, ",")) return Optional.empty();
    }

    return DeductionAlterDefinitions.createStep(_proof, Optional.of(_module), definitions);
  }

  /**
   * Helper function for createAddStep: this reads a single identifier, which should be the name
   * for a fresh variable.
   */
  private String readFreshName(CommandParsingStatus input, Renaming renaming) {
    int p = input.currentPosition();
    String varname = input.nextWord();
    if (varname == null || varname.equals("")) {
      _module.println("Unexpected end of input at position %a; I expected a variable name.", p);
      return null;
    }
    if (varname.indexOf('=') >= 0) {
      _module.println("Unexpected input at position %a.  Please use spaces around the = " +
        "in this command.", input.previousPosition());
      return null;
    }
    if (renaming.getReplaceable(varname) != null) {
      _module.println("Variable %a at position %a is already known in this equation " +
        "context.  Please choose a fresh name.", varname, input.previousPosition());
      return null;
    }
    return varname;
  }

  /**
   * Helper function for createAddStep: this reads exactly the given string from input, or throws
   * an error if that's not what the next word is.
   */
  private boolean expect(CommandParsingStatus input, String text) {
    if (input.commandEnded()) {
      _module.println("Unexpected end of input following token at position %a; I expected %a.",
        input.previousPosition(), text);
      return false;
    }
    String word = input.nextWord();
    if (!word.equals(text)) {
      _module.println("Unexpected input at position %a; I expected %a but got %a.",
        input.previousPosition(), text, word);
      return false;
    }
    return true;
  }

  /** Tab suggestions for this command are either variables, =, or a term. */
  @Override
  public ArrayList<TabSuggestion> suggestNext(String args) {
    ArrayList<TabSuggestion> ret = new ArrayList<TabSuggestion>();
    CommandParsingStatus status = new CommandParsingStatus(args);
    if (status.commandEnded()) { ret.add(new TabSuggestion("add", "keyword")); return ret; }
    status.nextWord();
    int kind = 1;
    while (kind > 0 && !status.commandEnded()) {
      if (kind == 1) {
        String name = status.nextWord();
        if (name == null || name.equals("") || name.indexOf('=') >= 0) kind = -1;
        else kind = 2;
      }
      else if (kind == 2) {
        String txt = status.nextWord();
        if (txt == null || !txt.equals("=")) kind = -1;
        else kind = 3;
      }
      else if (kind == 3) {
        if (status.skipTerm()) kind = 4;
        else break;
      }
      else {
        String txt = status.nextWord();
        if (txt == null || !txt.equals(",")) kind = -1;
        else kind = 1;
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
    return ret;
  }
}

