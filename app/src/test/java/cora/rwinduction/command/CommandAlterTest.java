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
import cora.rwinduction.engine.deduction.DeductionAlterDefinitions;
import cora.rwinduction.engine.deduction.DeductionAlterRename;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.parser.CommandParsingStatus;

class CommandAlterTest {
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

  private Optional<DeductionAlterDefinitions> createAddStep(OutputModule module, String str) {
    CommandAlter cmd = new CommandAlter();
    EquationContext ec =
      EquationParser.parseEquationData("sum1(x) = add(y,sum2(z)) | z ≥ y", trs, 3);
    PartialProof proof = new PartialProof(trs, FixedList.of(ec),
                                          lst -> module.generateUniqueNaming(lst));
    cmd.storeContext(proof, module);
    CommandParsingStatus status = new CommandParsingStatus(str);
    status.nextWord(); // alter
    status.nextWord(); // add
    return cmd.createAddStep(status);
  }

  @Test
  public void testSingleStep() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    DeductionAlterDefinitions step = createAddStep(module, "alter add a = x + y").get();
    assertTrue(step.toString().equals("alter add a = x + y"));
  }

  @Test
  public void testMultiStep() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    DeductionAlterDefinitions step =
      createAddStep(module, "alter add a = x + y, b = 0  , c = a + -b").get();
    assertTrue(step.toString().equals("alter add a = x + y, b = 0, c = a - b"));
  }

  @Test
  public void testMissingName() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createAddStep(module, "alter add ").isEmpty());
    assertTrue(createAddStep(module, "alter add a = x + y , ").isEmpty());
    assertTrue(module.toString().equals(
      "Parsing error at position 11: Expected fresh variable name but got end of input.\n\n" +
      "Parsing error at position 23: Expected fresh variable name but got end of input.\n\n"));
  }

  @Test
  public void testMissingEquals() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createAddStep(module, "alter add a").isEmpty());
    assertTrue(module.toString().equals(
      "Unexpected end of input following token at position 11; I expected =.\n\n"));
  }

  @Test
  public void testMissingValue() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createAddStep(module, "alter add a =").isEmpty());
    assertTrue(module.toString().equals(
      "Parsing error at position 14: Expected term, started by an identifier, λ, string or " +
      "(, but got end of input.\n\n"));
  }

  @Test
  public void testMissingComma() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createAddStep(module, "alter add a = x + y b = a + 1").isEmpty());
    assertTrue(module.toString().equals(
      "Unexpected input at position 21; I expected , but got b.\n\n"));
  }

  @Test
  public void testVariableAlreadyExists() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createAddStep(module, "alter add x  =  y + 1").isEmpty());
    assertTrue(module.toString().equals(
      "Variable x at position 11 is already known in this equation context.  " +
      "Please choose a fresh name.\n\n"));
  }

  @Test
  public void testUnknownVariableOnRight() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createAddStep(module, "alter add a=b + 1").isEmpty());
    assertTrue(module.toString().equals(
      "Unknown variable b in definition of a.\n\n"));
  }

  private Optional<DeductionAlterRename> createRenameStep(OutputModule module, String str) {
    CommandAlter cmd = new CommandAlter();
    EquationContext ec =
      EquationParser.parseEquationData("sum1(x) = add(y,sum2(z)) | z ≥ y", trs, 3);
    PartialProof proof = new PartialProof(trs, FixedList.of(ec),
                                          lst -> module.generateUniqueNaming(lst));
    cmd.storeContext(proof, module);
    CommandParsingStatus status = new CommandParsingStatus(str);
    status.nextWord(); // alter
    status.nextWord(); // rename
    return cmd.createRenameStep(status);
  }

  @Test
  public void testRename() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    DeductionAlterRename step =
      createRenameStep(module, "alter rename x := a , y:=b, z := c").get();
    assertTrue(step.toString().equals("alter rename x := a, y := b, z := c"));
  }

  @Test
  public void testRenameWithDoubleVariable() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createRenameStep(module, "alter rename x := a, y := a").isEmpty());
    assertTrue(module.toString().equals("The name a is already in use.\n\n"));
  }

  @Test
  public void testRenameWithMissingOriginal() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createRenameStep(module, "alter rename x := a, b := c").isEmpty());
    assertTrue(module.toString().equals("Unknown variable name: b.\n\n"));
  }

  @Test
  public void testRenameWithNonIdentifier() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createRenameStep(module, "alter rename x := a, y := 15").isEmpty());
    assertTrue(module.toString().equals(
      "Parsing error at position 27: Expected fresh variable name but got INTEGER (15).\n\n"));
  }

  @Test
  public void testRenameWithMissingColon() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createRenameStep(module, "alter rename x := a, y = b, z := c").isEmpty());
    assertTrue(module.toString().equals(
      "Unexpected input at position 24; I expected := but got =.\n\n"));
  }

  @Test
  public void testRenameWithMissingComma() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createRenameStep(module, "alter rename x := a y := b").isEmpty());
    assertTrue(module.toString().equals(
      "Unexpected input at position 21; I expected , but got y.\n\n"));
  }

  @Test
  public void testRenameEndingInComma() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createRenameStep(module, "alter rename x:=a ,").isEmpty());
    assertTrue(module.toString().equals("Parsing error at position 20: Expected existing " +
      "variable name but got end of input.\n\n"));
  }

  @Test
  public void testRenameEndingInAssign() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(createRenameStep(module, "alter rename x:=").isEmpty());
    assertTrue(module.toString().equals("Parsing error at position 17: Expected fresh variable " +
      "name but got end of input.\n\n"));
  }

  private ArrayList<Command.TabSuggestion> getSuggestions(String args) {
    CommandAlter cmd = new CommandAlter();
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
    assertTrue(suggestions.size() == 2);
    assertTrue(suggestions.get(0).text().equals("add"));
    assertTrue(suggestions.get(1).text().equals("rename"));
  }

  @Test
  public void testSuggestionOnlyAdd() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("add");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).text() == null);
    assertTrue(suggestions.get(0).category().equals("variable name"));
  }

  @Test
  public void testAddSuggestionOneNameGiven() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("add xa1hoa");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).text().equals("="));
    assertTrue(suggestions.get(0).category().equals("keyword"));
  }

  @Test
  public void testAddSuggestionBadGiven() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("add xa1h:a");
    assertTrue(suggestions.size() == 0);
  }

  @Test
  public void testAddSuggestionEqualGiven() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("add jdka = ");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).text() == null);
    assertTrue(suggestions.get(0).category().equals("term"));
  }

  @Test
  public void testAddSuggestionTermGiven() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("add jdka = x + 1");
    assertTrue(suggestions.size() == 3);
    assertTrue(suggestions.get(0).text() == null);
    assertTrue(suggestions.get(0).category().equals("rest of term"));
    assertTrue(suggestions.get(1).text().equals(","));
    assertTrue(suggestions.get(1).category().equals("keyword"));
    assertTrue(suggestions.get(2).text() == null);
    assertTrue(suggestions.get(2).category().equals("end of command"));
  }

  @Test
  public void testAddSuggestionWithoutSpaces() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("add xa1h=a");
    assertTrue(suggestions.size() == 3);
    assertTrue(suggestions.get(0).text() == null);
    assertTrue(suggestions.get(0).category().equals("rest of term"));
    assertTrue(suggestions.get(1).text().equals(","));
    assertTrue(suggestions.get(1).category().equals("keyword"));
    assertTrue(suggestions.get(2).text() == null);
    assertTrue(suggestions.get(2).category().equals("end of command"));
  }

  @Test
  public void testAddSuggestionPartialTermGiven() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("add jdka = x + 1 -");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).text() == null);
    assertTrue(suggestions.get(0).category().equals("term"));
  }

  @Test
  public void testAddSuggestionPastComma() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("add x = y + 1, ");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).text() == null);
    assertTrue(suggestions.get(0).category().equals("variable name"));
    suggestions = getSuggestions("add x = y + 1,");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).text() == null);
    assertTrue(suggestions.get(0).category().equals("variable name"));
  }

  @Test
  public void testSuggestionOnlyRename() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("rename");
    assertTrue(suggestions.size() == 2);
    assertTrue(suggestions.get(0).text().equals("y"));
    assertTrue(suggestions.get(0).category().equals("existing variable name"));
    assertTrue(suggestions.get(1).text().equals("z"));
    assertTrue(suggestions.get(1).category().equals("existing variable name"));
  }

  @Test
  public void testRenameSuggestionOneNameGiven() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("rename xa1hoa");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).text().equals(":="));
    assertTrue(suggestions.get(0).category().equals("keyword"));
  }

  @Test
  public void testRenameSuggestionAssignGiven() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("rename jdka:= ");
    assertTrue(suggestions.size() == 1);
    assertTrue(suggestions.get(0).text() == null);
    assertTrue(suggestions.get(0).category().equals("fresh variable name"));
  }

  @Test
  public void testRenameFirstPartGiven() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("rename jdka := bla,xx:=yy");
    assertTrue(suggestions.size() == 2);
    assertTrue(suggestions.get(0).text().equals(","));
    assertTrue(suggestions.get(0).category().equals("keyword"));
    assertTrue(suggestions.get(1).text() == null);
    assertTrue(suggestions.get(1).category().equals("end of command"));
  }

  @Test
  public void testRenameSuggestionPastComma() {
    ArrayList<Command.TabSuggestion> suggestions = getSuggestions("rename x := y, ");
    assertTrue(suggestions.size() == 2);
    assertTrue(suggestions.get(0).text().equals("y"));
    assertTrue(suggestions.get(0).category().equals("existing variable name"));
    assertTrue(suggestions.get(1).text().equals("z"));
    assertTrue(suggestions.get(1).category().equals("existing variable name"));
  }
}

