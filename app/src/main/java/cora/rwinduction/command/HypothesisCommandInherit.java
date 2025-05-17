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
import java.util.List;
import java.util.TreeSet;

import charlie.util.Pair;
import charlie.terms.FunctionSymbol;
import charlie.terms.Term;
import cora.rwinduction.engine.Equation;
import cora.rwinduction.engine.Hypothesis;
import cora.rwinduction.parser.CommandParsingStatus;

/** The shared functionality for CommandHypothesis and CommandHdelete. */
abstract class HypothesisCommandInherit extends ReductionCommandInherit {
  public HypothesisCommandInherit(String kind) {
    super(kind, "<name>[-inverse]");
  }

  @Override
  protected final void addTabSuggestionsForKind(TreeSet<FunctionSymbol> symbols,
                                                ArrayList<TabSuggestion> suggestions) {
    for (Hypothesis hypo : _proof.getProofState().getHypotheses()) {
      Equation eq = hypo.getEquation();
      if (!eq.getLhs().isFunctionalTerm() || symbols.contains(eq.getLhs().queryRoot())) {
        suggestions.add(new TabSuggestion(hypo.getName(), "hypothesis"));
      }
      if (!eq.getRhs().isFunctionalTerm() || symbols.contains(eq.getRhs().queryRoot())) {
        suggestions.add(new TabSuggestion(hypo.getName() + "-inverse", "hypothesis"));
      }
    }
  }

  @Override
  protected final Term getLeftFor(String hypoDesc) {
    Pair<String,Boolean> pair = splitHypothesisName(hypoDesc);
    Hypothesis hypothesis = _proof.getProofState().getHypothesisByName(pair.fst());
    if (hypothesis == null) return null;
    if (pair.snd()) return hypothesis.getEquation().getRhs();
    else return hypothesis.getEquation().getLhs();
  }

  /**
   * Helper function for run / createStep: this reads the next argument, and splits off a possible
   * "-inverse" part; then it checks that the hypothesis exists, and if so, returns a pair
   * representing first the hypothesis, and second the inverse status.
   */
  protected Pair<Hypothesis,Boolean> readHypothesis(CommandParsingStatus input) {
    String txt = input.nextWord();
    if (txt == null || txt.equals("")) {
      _module.println("Command " + _commandName + " should be invoked with at least 1 argument.");
      return null;
    }
    Pair<String,Boolean> pair = splitHypothesisName(txt);
    String name = pair.fst();
    boolean inverse = pair.snd();
    Hypothesis hypo = _proof.getProofState().getHypothesisByName(name);
    if (hypo == null) {
      _module.println("No such induction hypothesis: %a.", name);
      return null;
    }
    return new Pair<Hypothesis,Boolean>(hypo, inverse);
  }

  private Pair<String,Boolean> splitHypothesisName(String txt) {
    int len = txt.length();
    for (String str : List.of("^{-1}", "-inverse")) {
      int strlen = str.length();
      if (len > strlen && txt.substring(len - strlen).equals(str)) {
        return new Pair<String,Boolean>(txt.substring(0, len - strlen), true);
      }
    }
    return new Pair<String,Boolean>(txt, false);
  }
}

