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
import java.util.List;
import java.util.Set;

import charlie.util.FixedList;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.parser.CommandParsingStatus;

class CmdListTest {
  private PartialProof _proof = null;
  private OutputModule _module = null;

  private void setup() {
    if (_proof != null) return;
    TRS trs = CoraInputReader.readTrsFromString(
      "add :: Int -> Int -> Int\n" +
      "add(x,y) -> x + y\n");
    _module = cora.io.OutputModule.createUnicodeModule(trs);
    PartialProof proof = new PartialProof(trs,
      cora.rwinduction.parser.EquationParser.parseEquationList("add(x,y) = x + y", trs),
      lst -> _module.generateUniqueNaming(lst));
  }

  private class MyCommand extends Command {
    private String _name;
    public MyCommand(PartialProof p, OutputModule m, String name) {
      super(p, m);
      _name = name;
    }
    public String queryName() { return _name; }
    public FixedList<String> callDescriptor() { return FixedList.of(_name); }
    public void printHelp(OutputModule module) { }
    public List<TabSuggestion> suggestNext(String str) { return List.of(); }
    protected boolean run(CommandParsingStatus status) { return false; }
  }

  private MyCommand mcmd(String name) { return new MyCommand(_proof, _module, name); }

  @Test
  public void testRegistrationAndAliases() {
    CmdList lst = new CmdList();
    setup();
    lst.registerCommand(mcmd("simplify"));
    lst.registerAlias("simplification", "simplify");
    lst.registerAlias("simp", "simplify");
    lst.registerCommand(mcmd("delete"));
    assertTrue(lst.queryCommand("simplify").queryName().equals("simplify"));
    assertTrue(lst.queryCommand("simplification").queryName().equals("simplify"));
    assertTrue(lst.queryCommand("simp").queryName().equals("simplify"));
    assertTrue(lst.queryCommand("delete").queryName().equals("delete"));
    assertTrue(lst.queryCommands().size() == 2);
    assertTrue(lst.queryCommands().contains("simplify"));
    assertTrue(lst.queryCommands().contains("delete"));
    assertFalse(lst.queryCommands().contains("simplification"));
  }

  @Test
  public void testNonExisting() {
    CmdList lst = new CmdList();
    setup();
    lst.registerCommand(mcmd("simplify"));
    // command does not exist
    assertTrue(lst.queryCommand("simplification") == null);
    // wrong direction
    assertThrows(IllegalArgumentException.class, () ->
      lst.registerAlias("simplify", "simplification"));
  }

  @Test
  public void testIllegalOverride() {
    CmdList lst = new CmdList();
    setup();
    lst.registerCommand(mcmd("simplify"));
    lst.registerCommand(mcmd("delete"));
    lst.registerAlias("simp", "simplify");
    assertThrows(IllegalArgumentException.class, () -> lst.registerCommand(mcmd("simplify")));
    assertThrows(IllegalArgumentException.class, () -> lst.registerAlias("delete", "simplify"));
    assertThrows(IllegalArgumentException.class, () -> lst.registerCommand(mcmd("simp")));
    assertThrows(IllegalArgumentException.class, () -> lst.registerAlias("simp", "delete"));
  }
}

