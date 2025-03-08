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

import charlie.exceptions.CustomParserException;
import charlie.util.Pair;
import charlie.util.FixedList;
import charlie.terms.Renaming;
import charlie.terms.Substitution;
import charlie.terms.TermFactory;
import cora.rwinduction.engine.EquationPosition;
import cora.rwinduction.engine.Hypothesis;
import cora.rwinduction.engine.deduction.DeductionHypothesis;
import cora.rwinduction.parser.CommandParsingStatus;

/** The syntax for the deduction command hypothesis (simplification with an element of H). */
public class CommandHypothesis extends ReductionCommandInherit {
  public CommandHypothesis() {
    super("hypothesis", "<name>[-inverse]");
  }

  @Override
  public String helpDescriptor() {
    return "Use this deduction rule to rewrite the current equation with one of the current " +
           "induction hypotheses in the proof state, which might apply to some subterm of the " +
           "left- or right-hand side of the equation.  " +
           "Note that induction hypotheses can be found using :hypotheses, and that positions " +
           "have the form L.<position> or R.<position>.  " +
           "To use the inverse of an induction hypothesis, use for instance H5^{-1} or " +
           "H5-inverse.";
  }

  protected boolean run(CommandParsingStatus input) {
    Optional<DeductionHypothesis> step = createStep(input);
    if (step.isEmpty()) return false;
    return step.get().verifyAndExecute(_proof, Optional.of(_module));
  }

  /** Main functionality of run, separated out for the sake of unit testing. */
  Optional<DeductionHypothesis> createStep(CommandParsingStatus input) {
    // get induction hypothesis and inverse status
    Pair<Hypothesis,Boolean> hypopair = readHypothesis(input);
    if (hypopair == null) return Optional.empty();

    // get EquationPosition and Substitution
    Renaming hypoRenaming = hypopair.fst().getRenaming();
    Pair<EquationPosition,Substitution> restpair = readCommandRemainder(hypoRenaming, input);
    if (restpair == null) return Optional.empty();
    return DeductionHypothesis.createStep(_proof, Optional.of(_module), hypopair.fst(),
                                          hypopair.snd(), restpair.fst(), restpair.snd());
  }

  /**
   * Helper function for run / createStep: this reads the next argument, and splits off a possible
   * "-inverse" part; then it checks that the hypothesis exists, and if so, returns a pair
   * representing first the hypothesis, and second the inverse status.
   */
  private Pair<Hypothesis,Boolean> readHypothesis(CommandParsingStatus input) {
    String txt = input.nextWord();
    if (txt == null || txt.equals("")) {
      _module.println("Command hypothesis should be invoked with at least 1 argument.");
      return null;
    }
    String name = txt;
    boolean inverse = false;
    int len = txt.length();
    for (String str : List.of("^{-1}", "-inverse")) {
      int strlen = str.length();
      if (len > strlen && txt.substring(len - strlen).equals(str)) {
        name = txt.substring(0, len - strlen);
        inverse = true;
        break;
      }
    }
    Hypothesis hypo = _proof.getProofState().getHypothesisByName(name);
    if (hypo == null) {
      _module.println("No such induction hypothesis: %a.", name);
      return null;
    }
    return new Pair<Hypothesis,Boolean>(hypo, inverse);
  }
}

