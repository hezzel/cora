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

import charlie.parser.lib.ParsingStatus;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.engine.deduction.DeductionContext;
import cora.rwinduction.parser.CommandParsingStatus;
import cora.rwinduction.parser.EquationParser;

class CommandContextTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "g :: Int -> Int -> Int\n" +
      "g(x, y) -> g(x-1, y) | x > y");
  }

  private PartialProof setupProof(OutputModule module, String equation) {
    TRS trs = setupTRS();
    return new PartialProof(trs, EquationParser.parseEquationList(equation, trs),
      lst -> module.generateUniqueNaming(lst));
  }

  private DeductionContext createStep(PartialProof proof, OutputModule module, String str) {
    CommandContext cmd = new CommandContext();
    cmd.storeContext(proof, module);
    CommandParsingStatus status = new CommandParsingStatus(str);
    status.nextWord(); // :context
    return cmd.createStep(status);
  }

  @Test
  public void testSemiconstructorContext() {
    OutputModule module = OutputModule.createUnitTestModule();
    PartialProof pp = setupProof(module, "f(f(x, y), x + 3) -><- f(y, f(x-1, z)) | true");
    DeductionContext step = createStep(pp, module, "context");
    assertTrue(step.commandDescription().equals("semiconstructor"));
  }

  @Test
  public void testBasicContext() {
    OutputModule module = OutputModule.createUnitTestModule();
    PartialProof pp = setupProof(module, "g(f(x, y), x + 3) -><- g(y, f(x-1, z)) | true");
    DeductionContext step = createStep(pp, module, "context");
    assertTrue(step.commandDescription().equals("context"));
  }

  @Test
  public void testNonLexiPositions() {
    OutputModule module = OutputModule.createUnitTestModule();
    PartialProof pp = setupProof(module, "f(f(x, y), x + 3) -><- f(f(y, x+1), f(x-1, z)) | true");
    DeductionContext step = createStep(pp, module, "context 2 1.1 1.2");
    assertTrue(step.commandDescription().equals("context 2 1.1 1.2"));
  }

  @Test
  public void testBadPosition() {
    OutputModule module = OutputModule.createUnitTestModule();
    PartialProof pp = setupProof(module, "f(f(x, y), x + 3) -><- f(g(y, x+1), f(x-1, z)) | true");
    assertTrue(createStep(pp, module, "context L2 L1.1 L1.2") == null);
    assertTrue(module.toString().equals("Illegal position L2 (character 0): position index " +
      "should be an integer, but instead is [L2].\n\n"));
  }

  @Test
  public void testNotAGoodContext() {
    OutputModule module = OutputModule.createUnitTestModule();
    PartialProof pp = setupProof(module, "f(f(x, y), x + 3) -><- f(g(y, x+1), f(x-1, z)) | true");
    assertTrue(createStep(pp, module, "context 2 1.1 1.2") == null);
    assertTrue(module.toString().equals("The context rule is not applicable, since the subterms " +
      "at position 1 have different head terms (f and g).\n\n"));
  }

  @Test
  public void testSuggestionsEmpty() {
    OutputModule module = OutputModule.createUnitTestModule();
    PartialProof pp = setupProof(module, "f(f(x, y), x + 3) -><- f(g(x, y), f(x-1, z) + 4) | true");
    CommandContext cmd = new CommandContext();
    cmd.storeContext(pp, module);
    ArrayList<Command.TabSuggestion> arr = cmd.suggestNext("");
    assertTrue(arr.size() == 5);
    assertTrue(arr.get(0).text() == null);
    assertTrue(arr.get(0).category().equals("end of command"));
    assertTrue(arr.get(1).text().equals("1"));
    assertTrue(arr.get(1).category().equals("position"));
    assertTrue(arr.get(2).text().equals("2.1"));
    assertTrue(arr.get(2).category().equals("position"));
    assertTrue(arr.get(3).text().equals("2.2"));
    assertTrue(arr.get(3).category().equals("position"));
    assertTrue(arr.get(4).text().equals("2"));
    assertTrue(arr.get(4).category().equals("position"));
  }

  @Test
  public void testSuggestionsSomeGiven() {
    OutputModule module = OutputModule.createUnitTestModule();
    PartialProof pp = setupProof(module, "f(f(x, y), x + 3) -><- f(g(x, y), f(x-1, z) + 4) | true");
    CommandContext cmd = new CommandContext();
    cmd.storeContext(pp, module);
    ArrayList<Command.TabSuggestion> arr = cmd.suggestNext("1 2.3 2.2.ε");
    assertTrue(arr.size() == 3);
    assertTrue(arr.get(0).text() == null);
    assertTrue(arr.get(0).category().equals("end of command"));
    assertTrue(arr.get(1).text().equals("2.1"));
    assertTrue(arr.get(1).category().equals("position"));
    assertTrue(arr.get(2).text().equals("2"));
    assertTrue(arr.get(2).category().equals("position"));
  }
}

