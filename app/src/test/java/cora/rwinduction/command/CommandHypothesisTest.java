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

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import java.util.Optional;
import java.util.Set;

import charlie.util.Pair;
import charlie.util.FixedList;
import charlie.terms.replaceable.MutableRenaming;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;
import cora.rwinduction.engine.deduction.DeductionHypothesis;
import cora.rwinduction.engine.deduction.DeductionInduct;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.parser.CommandParsingStatus;

class CommandHypothesisTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "return :: Int -> result\n" +
      "error :: result\n" +
      "sum1 :: Int -> result\n" +
      "sum1(x) -> return(0) | x <= 0\n" +
      "sum1(x) -> add(x,sum1(x-1)) | x > 0\n" +
      "add :: Int -> result -> result\n" +
      "add(x, return(y)) -> return(x+y)\n" +
      "add(x, error) -> error\n" +
      "sum2 :: Int -> result\n" +
      "sum2(x) -> iter(x, 0, 0)\n" +
      "iter :: Int -> Int -> Int -> result\n" +
      "iter(x, i, z) -> return(z) | i > x\n" +
      "iter(x, i, z) -> iter(x, i+1, z+i) | i <= x\n");
  }

  private TRS _trs = setupTRS();

  private DeductionHypothesis createStep(OutputModule module, String str) {
    // set up a proof state with one equation and two hypotheses
    PartialProof proof = new PartialProof(_trs, EquationParser.parseEquationList(
      "add(0, sum1(x)) = sum2(x + 0) | x > 0", _trs), lst -> module.generateUniqueNaming(lst));
    Pair<Equation,MutableRenaming> hypo = EquationParser.parseEquation("sum1(x) = sum2(x)", _trs);
    ProofState state =
      proof.getProofState().addHypothesis(new Hypothesis(hypo.fst(), 12, hypo.snd()));
    hypo = EquationParser.parseEquation("sum2(x) = sum1(x) | x != y", _trs);
    state = state.addHypothesis(new Hypothesis(hypo.fst(), 29, hypo.snd()));
    proof.addProofStep(state, DeductionInduct.createStep(proof, Optional.empty()));

    // set up the command
    CommandHypothesis cmd = new CommandHypothesis();
    cmd.storeContext(proof, module);

    // create the step
    CommandParsingStatus status = new CommandParsingStatus(str);
    status.nextWord(); // hypothesis
    return cmd.createStep(status);
  }

  @Test
  public void testGoodStepWithoutSubstitution() {
    OutputModule module = OutputModule.createUnicodeModule(_trs);
    DeductionHypothesis step = createStep(module, "hypothesis H12 L.2");
    assertTrue(step.toString().equals("hypothesis H12 L2 with [x := x]"));
  }

  @Test
  public void testGoodInverseStepOnOtherSide() {
    OutputModule module = OutputModule.createUnicodeModule(_trs);
    DeductionHypothesis step = createStep(module, "hypothesis H12-inverse R");
    assertTrue(step.toString().equals("hypothesis H12^{-1} R with [x := x + 0]"));
  }

  @Test
  public void testGoodInverseStepWithSubstitution() {
    OutputModule module = OutputModule.createUnicodeModule(_trs);
    DeductionHypothesis step = createStep(module, "hypothesis H29^{-1} L.2 with [y := 17]");
    assertTrue(step.toString().equals("hypothesis H29^{-1} L2 with [x := x, y := 17]"));
  }

  @Test
  public void testNonExistingHypothesis() {
    OutputModule module = OutputModule.createUnicodeModule(_trs);
    assertTrue(createStep(module, "hypothesis H19 R.2") == null);
    assertTrue(module.toString().equals("No such induction hypothesis: H19.\n\n"));
  }

  @Test
  public void testNotAMatch() {
    OutputModule module = OutputModule.createUnicodeModule(_trs);
    assertTrue(createStep(module, "hypothesis H29 with [y:=x]") == null);
    assertTrue(module.toString().equals("The induction hypothesis does not apply due to failed " +
      "matching (matching debug info says Variable x has a different type from sum1(x).)\n\n"));
  }

  private ArrayList<Command.TabSuggestion> getSuggestions(String args) {
    OutputModule module = OutputModule.createUnicodeModule(_trs);
    PartialProof proof = new PartialProof(_trs, EquationParser.parseEquationList(
      "add(0, sum2(x)) = sum2(x + 0) | x > 0", _trs), lst -> module.generateUniqueNaming(lst));
    Pair<Equation,MutableRenaming> hypo = EquationParser.parseEquation("sum1(x) = sum2(x) | x != y", _trs);
    ProofState state =
      proof.getProofState().addHypothesis(new Hypothesis(hypo.fst(), 12, hypo.snd()));
    hypo = EquationParser.parseEquation("add(0, x) = error", _trs);
    state = state.addHypothesis(new Hypothesis(hypo.fst(), 29, hypo.snd()));
    proof.addProofStep(state, DeductionInduct.createStep(proof, Optional.empty()));
    CommandHypothesis cmd = new CommandHypothesis();
    cmd.storeContext(proof, module);
    return cmd.suggestNext(args);
  }

  @Test
  public void testSuggestionEmpty() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("");
    assertTrue(suggestions.size() == 2);
    suggestions = getSuggestions("     ");
    assertTrue(suggestions.size() == 2);
    assertTrue(suggestions.get(0).text().equals("H12-inverse"));
    assertTrue(suggestions.get(1).text().equals("H29"));
  }

  @Test
  public void testSuggestionsGivenHypothesis() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("H12-inverse");
    assertTrue(suggestions.size() == 2);
    assertTrue(suggestions.get(0).text().equals("L2"));
    assertTrue(suggestions.get(1).text().equals("R"));
    suggestions = getSuggestions("H29");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).text().equals("L"));
    assertTrue(getSuggestions("H29-inverse").size() == 0);
    assertTrue(getSuggestions("H17").size() == 0);
  }
}

