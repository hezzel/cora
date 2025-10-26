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
import java.util.Set;
import charlie.util.FixedList;
import charlie.util.Pair;
import charlie.terms.replaceable.*;
import charlie.terms.Term;
import charlie.substitution.MutableSubstitution;
import cora.io.OutputModule;
import cora.rwinduction.engine.DeductionStep;
import cora.rwinduction.engine.deduction.DeductionDisproveRoot;
import cora.rwinduction.engine.deduction.DeductionDisproveTheory;
import cora.rwinduction.engine.automation.AutoDisprover;
import cora.rwinduction.parser.CommandParsingStatus;

public class CommandDisprove extends DeductionCommand {
  @Override
  public String queryName() {
    return "disprove";
  }
  
  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of("disprove", "disprove root", "disprove theory",
                        "disprove theory with <substitution>");
  }

  @Override
  public void printHelp(OutputModule module) {
    module.println("Use this deduction rule to derive a contradiction: the initial set of " +
      "equations contains one that is NOT an inductive theorem.");
  }

  @Override
  public ArrayList<TabSuggestion> suggestNext(String args) {
    ArrayList<TabSuggestion> ret = new ArrayList<TabSuggestion>();
    String[] parts = args.strip().split("\\s+");
    if (parts.length == 0 || parts[0].equals("")) addNoArgumentsSuggestions(ret);
    else if (parts.length == 1) {
      if (parts[0].equals("root")) ret.add(endOfCommandSuggestion());
      if (parts[0].equals("theory")) {
        ret.add(endOfCommandSuggestion());
        ret.add(new TabSuggestion("with", "keyword"));
      }
    }
    else if (parts[1].equals("with")) addSubstitutionSuggestions(parts[parts.length-1], ret);
    return ret;
  }

  /** Helper function for suggestNext: used if the user has supplied only "disprove". */
  private void addNoArgumentsSuggestions(ArrayList<TabSuggestion> ret) {
    ret.add(endOfCommandSuggestion());
    if (_proof.getProofState().getTopEquation().getLhs().isTheoryTerm() &&
        _proof.getProofState().getTopEquation().getRhs().isTheoryTerm() &&
        _proof.getProofState().getTopEquation().getLhs().queryType().isBaseType()) {
      ret.add(new TabSuggestion("theory", "keyword"));
    }
    else ret.add(new TabSuggestion("root", "keyword"));
  }

  /** Helper function for suggestNext: used to suggest the user may want to supply a substituion */
  private void addSubstitutionSuggestions(String lastWord, ArrayList<TabSuggestion> ret) {
    if (!lastWord.equals("") && lastWord.charAt(lastWord.length()-1) == ']') {
      ret.add(endOfCommandSuggestion());
    }
    else ret.add(new TabSuggestion(null, "substitution"));
  }

  @Override
  protected DeductionStep createStep(CommandParsingStatus input) {
    if (input.commandEnded()) return AutoDisprover.createStep(_proof, optionalModule());
    String word = input.nextWord();
    if (word.equals("root")) return createRootStep(input);
    else if (word.equals("theory")) return createTheoryStep(input);
    else {
      _module.println("Unexpected argument at position %a: expected \"root\" or \"theory\" " +
        "(or end of command).", input.previousPosition());
    }
    return null;
  }

  private DeductionDisproveRoot createRootStep(CommandParsingStatus input) {
    if (!input.commandEnded()) {
      _module.println("Unexpected argument at position %a: disprove root command should " +
        "end after the \"root\".", input.currentPosition());
      return null;
    }
    return DeductionDisproveRoot.createStep(_proof, optionalModule());
  }

  private DeductionStep createTheoryStep(CommandParsingStatus input) {
    if (input.commandEnded()) return AutoDisprover.createTheoryStep(_proof, optionalModule());
    if (!input.expect("with", optionalModule())) return null;
    if (_proof.getProofState().isFinalState()) {
      _module.println("The proof state is empty; there is nothing to disprove.");
      return null;
    }   
    Renaming keyNames = _proof.getProofState().getTopEquation().getRenaming();
    MutableRenaming valueNames = new MutableRenaming(Set.of());
    MutableSubstitution subst = input.readSubstitution(_proof.getContext().getTRS(), keyNames,
                                                                          valueNames, _module);
    if (subst == null) return null;
    for (Replaceable x : keyNames.domain()) {
      Term result = subst.get(x);
      if (result == null) {
        _module.println("The substitution should map ALL variables of the equation; missing %a.",
          keyNames.getName(x));
        return null;
      }
      if (!subst.get(x).isGround() || !subst.get(x).isTheoryTerm()) {
        _module.println("Illegal mapping [%a := %a]: the substitution should map to ground " +
          "theory terms.", keyNames.getName(x), new Pair<Term,Renaming>(subst.get(x), valueNames));
        return null;
      }
    }
    return DeductionDisproveTheory.createStep(_proof, optionalModule(), subst);
  }
}

