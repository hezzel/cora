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

import charlie.util.FixedList;
import charlie.terms.TheoryFactory;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.rwinduction.engine.EquationContext;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.engine.deduction.DeductionSimplify;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.parser.CommandParsingStatus;

class CommandSimplifyTest {
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

  private TRS trs = setupTRS();

  private DeductionSimplify createStep(OutputModule module, String str) {
    CommandSimplify cmd = new CommandSimplify();
    EquationContext ec =
      EquationParser.parseEquationData("sum1(z) = add(y,sum2(z)) | z ≥ 0 ∧ y < 0", trs, 1);
    PartialProof proof = new PartialProof(trs, FixedList.of(ec),
                                          lst -> module.generateUniqueNaming(lst));
    cmd.storeContext(proof, module);
    CommandParsingStatus status = new CommandParsingStatus(str);
    status.nextWord(); // simplify
    return cmd.createStep(status);
  }

  private boolean execute(OutputModule module, String str) {
    CommandSimplify cmd = new CommandSimplify();
    EquationContext ec =
      EquationParser.parseEquationData("sum1(z) = add(y,sum2(z)) | z ≥ 0 ∧ y < 0", trs, 1);
    PartialProof proof = new PartialProof(trs, FixedList.of(ec),
                                          lst -> module.generateUniqueNaming(lst));
    cmd.storeContext(proof, module);
    CommandParsingStatus status = new CommandParsingStatus(str);
    status.nextWord(); // simplify
    return cmd.execute(status);
  }

  @Test
  public void testGoodStepWithoutSubstitution() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    DeductionSimplify step = createStep(module, "simplify R5 r.2");
    assertTrue(step.toString().equals("simplify R5 r2 with [x := z]"));
  }

  @Test
  public void testGoodStepWithSubstitution() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    DeductionSimplify step = createStep(module, "simplify R1 with [x:=z]");
    assertTrue(step.toString().equals("simplify R1 l with [x := z]"));
  }

  @Test
  public void testNonExistingRule() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createStep(module, "simplify R19 r.2") == null);
    assertTrue(module.toString().equals("No such rule: R19\n\n"));

    module = OutputModule.createUnicodeModule(trs);
    assertFalse(execute(module, "simplify 5 r.2"));
    assertTrue(module.toString().equals("No such rule: 5\n\n"));
  }

  @Test
  public void testBadPosition() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createStep(module, "simplify R5 l1.2.3.2 with [x:=1]") == null);
    assertTrue(module.toString().equals("No such position: l1.2.3.2.\n\n"));
  }

  @Test
  public void testBadSubstitution() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createStep(module, "simplify R5 r.2 with [x:=1]") == null);
    assertTrue(module.toString().equals(
      "The rule does not apply due to failed matching (matching debug info says: " +
      "Variable x is mapped both to 1 and to z.)\n\n"));
  }

  @Test
  public void testOmitWith() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertFalse(execute(module, "simplify R5 r.2 [x:=z]"));
    assertTrue(module.toString().equals("Unexpected argument at position 17: expected \"with\" " +
      "or end of command, but got [x:=z].\n\n"));
  }

  @Test
  public void testTextAfterSubstitution() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createStep(module, "simplify R1 with [x:=z] o") == null);
    assertTrue(module.toString().equals("Unexpected argument at position 25: " +
      "expected end of command.\n\n"));
  }

  private ArrayList<Command.TabSuggestion> getSuggestions(String args) {
    CommandSimplify cmd = new CommandSimplify();
    EquationContext ec =
      EquationParser.parseEquationData("sum1(z) = add(y,sum2(z+1)) | z ≥ 0 ∧ y < 0", trs, 1);
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof proof = new PartialProof(trs, FixedList.of(ec),
                                          lst -> module.generateUniqueNaming(lst));
    cmd.storeContext(proof, module);
    return cmd.suggestNext(args);
  }

  @Test
  public void testSuggestionEmpty() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("");
    assertTrue(suggestions.size() == 5);  // the rules for add, sum1, sum2
    suggestions = getSuggestions("     ");
    assertTrue(suggestions.size() == 5);
  }

  @Test
  public void testSuggestionsGivenRule() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("R2");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).text().equals("l"));
    suggestions = getSuggestions("R5");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).text().equals("r2"));
    assertTrue(getSuggestions("R6").size() == 0); // different root symbol
    assertTrue(getSuggestions("R3").size() == 0); // same root symbol, but no match
  }

  @Test
  public void testSuggestionsGivenRuleAndWith() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("R2 with");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).text() == null);
    assertTrue(suggestions.get(0).category().equals("substitution"));
    suggestions = getSuggestions("R2 with [aa");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).text() == null);
    assertTrue(suggestions.get(0).category().equals("substitution"));
    suggestions = getSuggestions("R2 r12.34 with [aa");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).text() == null);
    assertTrue(suggestions.get(0).category().equals("substitution"));
    suggestions = getSuggestions("R2 r12.34 with");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).category().equals("substitution"));
  }

  @Test
  public void testSuggetionsGivenSubstitution() {
    ArrayList<Command.TabSuggestion> suggestions;
    suggestions = getSuggestions("R2 r12.34 with [aa]");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).text() == null);
    assertTrue(suggestions.get(0).category().equals("end of command"));
    suggestions = getSuggestions("R2 r12.34 [aa]");
    assertTrue(suggestions.size() == 0);
    suggestions = getSuggestions("R2 with [aa]");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).category().equals("end of command"));
  }
}

