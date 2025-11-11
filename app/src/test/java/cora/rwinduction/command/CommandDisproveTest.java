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

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import java.util.Optional;
import java.util.Set;

import charlie.util.FixedList;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.smt.*;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.EquationContext;
import cora.rwinduction.engine.DeductionStep;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.parser.CommandParsingStatus;

class CommandDisproveTest {
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
      "double :: Int -> Int\n" +
      "double(x) -> x * 2\n");
  }

  private TRS trs = setupTRS();

  private DeductionStep createStep(OutputModule module, String equation, String txt) {
    CommandDisprove cmd = new CommandDisprove();
    PartialProof proof = new PartialProof(trs, EquationParser.parseEquationList(equation, trs),
      lst -> module.generateUniqueNaming(lst));
    cmd.storeContext(proof, module);
    CommandParsingStatus status = new CommandParsingStatus(txt);
    status.nextWord(); // disprove
    return cmd.createStep(status);
  }

  @Test
  public void testGoodRootStep() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    DeductionStep step = createStep(module, "return(z) = error | z ≥ 0", "disprove root");
    assertTrue(step.commandDescription().equals("disprove root"));
  }

  @Test
  public void testUnspecifiedRootStep() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    DeductionStep step = createStep(module, "return(0) = x | true", "disprove");
    assertTrue(step.commandDescription().equals("disprove root"));
  }

  @Test
  public void testBadRootStep() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createStep(module, "return(3) = return(2) | true", "disprove root") == null);
    assertTrue(module.toString().equals("Both sides have the same root symbol.\n\n"));
  }

  @Test
  public void testAutomaticTheory() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Settings.smtSolver =
      new ProgrammableSmtSolver("i1 + i2 # 1 + i2", new SmtSolver.Answer.YES(new Valuation()));
    DeductionStep step =
      createStep(module, "{ F :: Int -> Int } F(x) = 1 + x | true", "disprove theory");
    assertTrue(step.commandDescription().equals("disprove theory with [F := [+](4242), x := 4242]"));
  }

  @Test
  public void testMisspelledWith() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createStep(module, "x + 1 = x | true", "disprove theory wiht [x := 1]") == null);
    assertTrue(module.toString().equals(
      "Unexpected input at position 17; I expected with but got wiht.\n\n"));
  }

  @Test
  public void testLegalTheoryWith() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Settings.smtSolver = null;
    DeductionStep step =
      createStep(module, "{ F :: Int -> Int } F(x) = 1 + x | true",
                         "disprove theory with [F := [*](0),x := 3]");
    assertTrue(step.commandDescription().equals("disprove theory with [F := [*](0), x := 3]"));
  }

  @Test
  public void testMissingVariable() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Settings.smtSolver = null;
    assertTrue(createStep(module, "{ F :: Int -> Int } F(x) = 1 + x | true",
                                  "disprove theory with [F := [*](0)]") == null);
    assertTrue(module.toString().equals("The substitution should map ALL variables of the " +
      "equation; missing x.\n\n"));
  }

  @Test
  public void testNonTheoryMapping() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Settings.smtSolver = null;
    assertTrue(createStep(module, "{ x :: Int } x = y | x > 0 ∧ y > 0",
                                  "disprove theory with [x := 1, y := double(1)]") == null);
    assertTrue(module.toString().equals("Illegal mapping [y := double(1)]: the substitution " +
      "should map to ground theory terms.\n\n"));
  }

  @Test
  public void testNonGroundMapping() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Settings.smtSolver = null;
    assertTrue(createStep(module, "{ x :: Int } x = y | x > 0 ∧ y > 0",
                                  "disprove theory with [x := 1, y := 1 + z]") == null);
    assertTrue(module.toString().equals("Illegal mapping [y := 1 + z]: the substitution " +
      "should map to ground theory terms.\n\n"));
  }

  private ArrayList<Command.TabSuggestion> getSuggestions(String eq, String args) {
    CommandDisprove cmd = new CommandDisprove();
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof proof = new PartialProof(trs, EquationParser.parseEquationList(eq, trs),
      lst -> module.generateUniqueNaming(lst));
    cmd.storeContext(proof, module);
    return cmd.suggestNext(args);
  }

  @Test
  public void testSuggestionEmptyTheory() {
    ArrayList<Command.TabSuggestion> suggestions =
      getSuggestions("x + y = 2 * z | x = z - y", "");
    assertTrue(suggestions.size() == 2);
    suggestions = getSuggestions("x + y = 2 * z | x = z - y", "     ");
    assertTrue(suggestions.size() == 2);
    assertTrue(suggestions.get(0).category().equals("end of command"));
    assertTrue(suggestions.get(1).category().equals("keyword"));
    assertTrue(suggestions.get(1).text().equals("theory"));
  }

  @Test
  public void testSuggestionEmptyNonTheory() {
    ArrayList<Command.TabSuggestion> suggestions =
      getSuggestions("double(x + y) = 2 * z | x = z - y", "");
    assertTrue(suggestions.size() == 2);
    assertTrue(suggestions.get(0).category().equals("end of command"));
    assertTrue(suggestions.get(1).category().equals("keyword"));
    assertTrue(suggestions.get(1).text().equals("root"));
  }

  @Test
  public void testSuggestionRoot() {
    ArrayList<Command.TabSuggestion> suggestions =
      getSuggestions("{ F :: Int -> Int } double(x + y) = F(z) | x = z - y", "  root ");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).category().equals("end of command"));
  }

  @Test
  public void testSuggestionTheory() {
    ArrayList<Command.TabSuggestion> suggestions =
      getSuggestions("x + y = 2 * z | x = z - y", "theory");
    assertTrue(suggestions.size() == 2);
    assertTrue(suggestions.get(0).category().equals("end of command"));
    assertTrue(suggestions.get(1).category().equals("keyword"));
    assertTrue(suggestions.get(1).text().equals("with"));
  }

  @Test
  public void testSuggestionSubstitution() {
    ArrayList<Command.TabSuggestion> suggestions =
      getSuggestions("{ F :: Int -> Int } F(x) + y = 2 * y | x > y", "theory with");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).category().equals("substitution"));
    assertTrue(suggestions.get(0).text() == null);
    suggestions =
      getSuggestions("{ F :: Int -> Int } F(x) + y = 2 * y | x > y", "theory with [ x := y,");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).category().equals("substitution"));
    suggestions =
      getSuggestions("{ F :: Int -> Int } F(x) + y = 2 * y | x > y", "theory with [ x := y]");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).category().equals("end of command"));
  }
}

