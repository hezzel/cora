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
import java.util.Set;

import charlie.util.FixedList;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.parser.CommandParsingStatus;
import cora.rwinduction.parser.EquationParser;

class CommandHelpTest {
  TRS trs = CoraInputReader.readTrsFromString(
    "sum1 :: Int -> result\n" +
    "sum2 :: Int -> result\n");

  private PartialProof createPP(OutputModule module) {
    return new PartialProof(trs,
      EquationParser.parseEquationList("sum1(x) = sum2(x) | x ≥ 0", trs),
      lst -> module.generateUniqueNaming(lst));
  }

  private CmdList makeCmdList() {
    CmdList lst = new CmdList();
    lst.registerCommand(new CommandQuit());
    lst.registerCommand(new CommandRules());
    lst.registerCommand(new CommandDelete());
    lst.registerCommand(new CommandHelp(lst));
    return lst;
  }

  private boolean runCommand(OutputModule module, String str) {
    CommandHelp cmd = new CommandHelp(makeCmdList());
    PartialProof pp = createPP(module);
    cmd.storeContext(pp, module);
    CommandParsingStatus status = new CommandParsingStatus(str);
    status.nextWord();  // skip past :help
    boolean ret = cmd.execute(status);
    assertTrue(status.commandEnded());
    return ret;
  }

  @Test
  public void testHelpPlain() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    runCommand(module, ":help");
    assertTrue(module.toString().equals(
    "Welcome to the interactive equivalence prover!\n\n" +
    "  To list available commands, use: :help commands\n" +
    "  To get out of the prover, use    :quit\n\n"));
  }

  @Test
  public void testHelpCommands() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    runCommand(module, ":help   commands");
    assertTrue(module.toString().equals(
      "You can use the following commands to interact with the prover:\n\n" +
      "  Prover commands: :help :quit :rules \n" +
      "  Deduction rules: delete \n\n"));
  }

  @Test
  public void testHelpSingle() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    runCommand(module, ":help :help");
    assertTrue(module.toString().equals(
      "Prints a short description to explain how the prover works.\n\n" +
      "  :help\n" +
      "  :help commands\n" +
      "  :help <command>\n\n"));
  }

  @Test
  public void testBadInvocation() {
    Command cmd = new CommandHelp(makeCmdList());
    OutputModule module = OutputModule.createUnicodeModule(trs);
    cmd.storeContext(createPP(module), module);
    assertFalse(cmd.execute(new CommandParsingStatus("quit")));
    assertTrue(module.toString().equals("Unknown command: quit\n\n"));
    assertFalse(cmd.execute(new CommandParsingStatus(":quit :help")));
    assertTrue(module.toString().equals(
      "Unknown command: quit\n\n" +
      "Unexpected argument at position 7: :help takes at most 1 argument.\n\n"));
  }
}

